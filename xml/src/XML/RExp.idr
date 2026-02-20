module XML.RExp

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
import Data.String
import Derive.Prelude
import FS.Posix
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import Syntax.T1
import Text.ILex.Derive
import Text.ILex.FS

import public Text.ILex

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Globally Forbidden Characters
--------------------------------------------------------------------------------

export
forbidden : RExp True
forbidden = -- basic control blocks
            range32 0x00 0x08 <|>
            range32 0x0b 0x0c <|>
            range32 0x0e 0x1f <|>
            -- DEL + C1 controls
            range32 0x7f 0x84 <|>
            range32 0x86 0x9f <|>
            -- UTF-16 surrogate block
            range32 0xd800 0xdfff <|>
            -- unicode characters (fixed block)
            range32 0xfdd0 0xfdef <|>
            -- non-characters at end of each unicode plane
            range32 0xfffe 0xffff <|>
            range32 0x1fffe 0x1ffff <|>
            range32 0x2fffe 0x2ffff <|>
            range32 0x3fffe 0x3ffff <|>
            range32 0x4fffe 0x4ffff <|>
            range32 0x5fffe 0x5ffff <|>
            range32 0x6fffe 0x6ffff <|>
            range32 0x7fffe 0x7ffff <|>
            range32 0x8fffe 0x8ffff <|>
            range32 0x9fffe 0x9ffff <|>
            range32 0xafffe 0xaffff <|>
            range32 0xbfffe 0xbffff <|>
            range32 0xcfffe 0xcffff <|>
            range32 0xdfffe 0xdffff <|>
            range32 0xefffe 0xeffff <|>
            range32 0xffffe 0xfffff <|>
            range32 0x10fffe 0x10ffff

--------------------------------------------------------------------------------
--          Char
--------------------------------------------------------------------------------

export
char : RExp True
char = range32 0x0009 0x0009 <|>
       range32 0x000a 0x000a <|>
       range32 0x000d 0x000d <|>
       range32 0x0020 0xd7ff <|>
       range32 0xe000 0xfffd <|>
       range32 0x10000 0x10ffff

--------------------------------------------------------------------------------
--          S
--------------------------------------------------------------------------------

export
whitespace : RExp True
whitespace = range32 0x0020 0x0020 <|>
             range32 0x0009 0x0009 <|>
             range32 0x000d 0x000d <|>
             range32 0x000a 0x000a

--------------------------------------------------------------------------------
--          EncName
--------------------------------------------------------------------------------

export
encname : RExp True
encname = ( range32 0x0041 0x005a <|>
            range32 0x0061 0x007a <|>
          ) >>
          ( range32 0x002d 0x002d <|>
            range32 0x002e 0x002e <|>
            range32 0x0030 0x0039 <|>
            range32 0x0041 0x005a <|>
            range32 0x005f 0x005f <|>
            range32 0x0061 0x007a
          )

--------------------------------------------------------------------------------
--          NameStartChar
--------------------------------------------------------------------------------

export
namestartchar : RExp True
namestartchar = range32 0x003a 0x003a <|>
                range32 0x005f 0x005f <|>
                range32 0x0041 0x005a <|>
                range32 0x0061 0x007a <|>
                range32 0x00c0 0x00d6 <|>
                range32 0x00d8 0x00f6 <|>
                range32 0x00f8 0x02ff <|>
                range32 0x0370 0x037d <|>
                range32 0x037f 0x1fff <|>
                range32 0x200c 0x200d <|>
                range32 0x2070 0x218f <|>
                range32 0x2c00 0x2fef <|>
                range32 0x3001 0xd7ff <|>
                range32 0xf900 0xfdcf <|>
                range32 0xfdf0 0xfffd <|>
                range32 0x10000 0xeffff

--------------------------------------------------------------------------------
--          NameChar
--------------------------------------------------------------------------------

export
namechar : RExp True
namechar = namestartchar <|>
           range32 0x002d 0x002d <|>
           range32 0x002e 0x002e <|>
           range32 0x0030 0x0039 <|>
           range32 0x00b7 0x00b7 <|>
           range32 0x0300 0x036f <|>
           range32 0x203f 0x2040

--------------------------------------------------------------------------------
--          Name
--------------------------------------------------------------------------------

export
name : RExp True
name = namestartchar >> (star namechar)

--------------------------------------------------------------------------------
--          PubidChar
--------------------------------------------------------------------------------          

export
pubidchar : RExp True
pubidchar = range32 0x000a 0x000a <|>
            range32 0x000d 0x000d <|>
            range32 0x0020 0x0020 <|>
            range32 0x0021 0x0021 <|>
            range32 0x0023 0x0023 <|>
            range32 0x0024 0x0025 <|>
            range32 0x0027 0x0029 <|>
            range32 0x002a 0x002a <|>
            range32 0x002b 0x002c <|>
            range32 0x002d 0x002d <|>
            range32 0x002e 0x002f <|>
            range32 0x0030 0x0039 <|>
            range32 0x003a 0x003b <|>
            range32 0x003d 0x003d <|>
            range32 0x003f 0x003f <|>
            range32 0x0040 0x0040 <|>
            range32 0x0041 0x005a <|>
            range32 0x005f 0x005f <|>
            range32 0x0061 0x007a
