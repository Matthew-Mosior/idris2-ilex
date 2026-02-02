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
  NL                              : ByteString -> XMLValue
  XMLDeclVersion                  : ByteString -> XMLValue
  XMLDeclEncoding                 : ByteString -> XMLValue
  XMLDeclStandalone               : Bool -> XMLValue
  XMLDeclComment                  : ByteString -> XMLValue
  XMLDeclProcessingInstruction    : ByteString -> XMLValue
  XMLDocType                      : ByteString -> XMLValue
  XMLDocTypeComment               : ByteString -> XMLValue
  XMLDocTypeProcessingInstruction : ByteString -> XMLValue
  XMLElementAttribute             : ByteString -> XMLValue
  XMLElementCharData              : ByteString -> XMLValue
  XMLElementComment               : ByteString -> XMLValue
  XMLElementProcessingInstruction : ByteString -> XMLValue


--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "XMLSz" "XMLST"
  ["XMLIni", "XMLDeclS", "XMLDeclMisc", "XMLDeclMiscComment", "FHdrDone", "FD", "FDNL", "FEmpty", "FComplete"]

%runElab derive "XMLValue" [Show,Eq]
