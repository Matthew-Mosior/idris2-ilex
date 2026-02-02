module XML.Parser

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
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
--          XMLValue
--------------------------------------------------------------------------------

public export
data XMLValue : Type where
  NL          : ByteString -> FASTAValue



%runElab derive "XMLValue" [Show,Eq]
