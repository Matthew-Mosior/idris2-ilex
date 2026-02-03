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
--          XMLValues
--------------------------------------------------------------------------------

public export
record XMLValues where
  constructor MkXMLValues
  nr     : Nat
  values : List XMLValue

%runElab derive "XMLValues" [Show,Eq]

Interpolation XMLValues where interpolate = show

--------------------------------------------------------------------------------
--          XMLDocument
--------------------------------------------------------------------------------

public export
0 XMLDocument : Type
XMLDocument = List XMLValues

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

public export
record XMLSTCK (q : Type) where
  constructor F
  line      : Ref q Nat
  col       : Ref q Nat
  psns      : Ref q (SnocList Position)
  strs      : Ref q (SnocList String)
  err       : Ref q (Maybe $ BoundedErr Void)
  xmlvalues : Ref q (SnocList XMLValue)
  xmldoc    : Ref q (SnocList XMLValues)
  bytes     : Ref q ByteString

export %inline
HasPosition XMLSTCK where
  line      = FSTCK.line
  col       = FSTCK.col
  positions = FSTCK.psns

export %inline
HasError XMLSTCK Void where
  error = err

export %inline
HasStringLits XMLSTCK where
  strings = strs

export %inline
HasStack XMLSTCK (SnocList XMLValues) where
  stack = xmldoc

export %inline
HasBytes XMLSTCK where
  bytes = XMLSTCK.bytes

export
xmlinit : F1 q (XMLSTCK q)
xmlinit = T1.do
  l  <- ref1 Z
  c  <- ref1 Z
  bs <- ref1 [<]
  ss <- ref1 [<]
  er <- ref1 Nothing
  xmlvs <- ref1 [<]
  xmlls <- ref1 [<]
  by <- ref1 ""
  pure (F l c bs ss er xmlvs xmlls fc by)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "XMLSz" "XMLST"
  ["XMLIni", "XMLDeclS", "XMLDeclMisc", "XMLDeclMiscComment", "FHdrDone", "FD", "FDNL", "XMLEmpty", "XMLComplete"]

%runElab derive "XMLValue" [Show,Eq]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FBroken $ unexpected ["character other than '>'"]
    , E FEmpty $ unexpected ["sequence data"]
    , E FHdr $ unexpected ["sequence line"]
    ]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFASTAValueHdrS : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueHdrS v = push1 x.fastavalues v >> pure FHdrToNLS

onFASTAValueHdrR : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueHdrR v = push1 x.fastavalues v >> pure FHdrToNLR

onFASTAValueAdenine : (x : FSTCK q) => F1 q FST
onFASTAValueAdenine = T1.do
  fc <- read1 x.fastacounter
  push1 x.fastavalues (Adenine fc) >> write1 x.fastacounter (S fc) >> pure FD

onFASTAValueThymine : (x : FSTCK q) => F1 q FST
onFASTAValueThymine = T1.do
  fc <- read1 x.fastacounter
  push1 x.fastavalues (Thymine fc) >> write1 x.fastacounter (S fc) >> pure FD

onFASTAValueGuanine : (x : FSTCK q) => F1 q FST
onFASTAValueGuanine = T1.do
  fc <- read1 x.fastacounter
  push1 x.fastavalues (Guanine fc) >> write1 x.fastacounter (S fc) >> pure FD

onFASTAValueCytosine : (x : FSTCK q) => F1 q FST
onFASTAValueCytosine = T1.do
  fc <- read1 x.fastacounter
  push1 x.fastavalues (Cytosine fc) >> write1 x.fastacounter (S fc) >> pure FD

onNLFHdr : (x : FSTCK q) => ByteString -> F1 q FST
onNLFHdr v = T1.do
  incline 1
  push1 x.fastavalues (NL v)
  fvs@(_::_) <- getList x.fastavalues | [] => pure FEmpty
  case Prelude.any isHeader fvs && Prelude.any isData fvs of
    True  => pure FBroken
    False => T1.do
      ln <- read1 x.line
      push1 x.fastalines (MkFASTALine ln fvs)
      pure FHdrDone

onNLFD : (x : FSTCK q) => ByteString -> F1 q FST
onNLFD v = T1.do
  incline 1
  push1 x.fastavalues (NL v)
  fvs@(_::_) <- getList x.fastavalues | [] => pure FEmpty
  case Prelude.any isHeader fvs && Prelude.any isData fvs of
    True  => pure FBroken
    False => T1.do
      ln <- read1 x.line
      push1 x.fastalines (MkFASTALine ln fvs)
      pure FDNL

onEOI : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onEOI = T1.do
  incline 1
  fvs@(_::_) <- getList x.fastavalues
    | [] => arrFail FSTCK fastaErr FEmpty x
  ln <- read1 x.line
  push1 x.fastalines (MkFASTALine ln fvs)
  pure (Right FComplete)

fastaInit : DFA q FSz FSTCK
fastaInit =
  dfa
    [ read '>' (\_ => onFASTAValueHdrS HeaderStart)
    ]

fastaHdrStrStart : DFA q FSz FSTCK
fastaHdrStrStart =
  dfa
    [ read dot (onFASTAValueHdrR . HeaderValue)
    ]

fastaHdrStrRest : DFA q FSz FSTCK
fastaHdrStrRest =
  dfa
    [ read dot (onFASTAValueHdrR . HeaderValue)
    , conv linebreak (\bs => onNLFHdr bs)
    ]

fastaFDInit : DFA q FSz FSTCK
fastaFDInit =
  dfa
    [ read adenine (\_ => onFASTAValueAdenine)
    , read thymine (\_ => onFASTAValueThymine)
    , read guanine (\_ => onFASTAValueGuanine)
    , read cytosine (\_ => onFASTAValueCytosine)
    ]

fastaFD : DFA q FSz FSTCK
fastaFD =
  dfa
    [ conv linebreak (\bs => onNLFD bs)
    , read adenine (\_ => onFASTAValueAdenine)
    , read thymine (\_ => onFASTAValueThymine)
    , read guanine (\_ => onFASTAValueGuanine)
    , read cytosine (\_ => onFASTAValueCytosine)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FIni fastaInit
    , E FHdrToNLS fastaHdrStrStart
    , E FHdrToNLR fastaHdrStrRest
    , E FHdrDone fastaFDInit
    , E FDNL fastaFDInit
    , E FD fastaFD
    ]

fastaEOI : FST -> FSTCK q -> F1 q (Either (BoundedErr Void) FASTA)
fastaEOI st x =
  case st == FIni || st == FHdr || st == FEmpty || st == FBroken of
    True  => arrFail FSTCK fastaErr st x
    False => T1.do
      _ <- onEOI
      fasta <- getList x.fastalines
      pure (Right fasta)

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

export
xml : P1 q (BoundedErr Void) XMLSz XMLSTCK XMLDocument
xml = P XMLIni xmlinit xmlSteps snocChunk xmlErr xmlEOI

export %inline
parseXML : Origin -> String -> Either (ParseError Void) XMLDocument
parseXML = parseString xml

--------------------------------------------------------------------------------
--          Streaming
--------------------------------------------------------------------------------

streamXML :  String
          -> AsyncPull Poll Void [ParseError Void, Errno] ()
streamXML pth =
     readBytes pth
  |> streamParse xml (FileSrc pth)
  |> C.count
  |> printLnTo Stdout

streamXMLDocuments :  AsyncPull Poll String [ParseError Void, Errno] ()
                   -> AsyncPull Poll Void [ParseError Void, Errno] ()
streamXMLDocuments pths =
     flatMap pths (\p => readBytes p |> streamParse xml (FileSrc p))
  |> C.count
  |> printLnTo Stdout
