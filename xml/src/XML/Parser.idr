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
  XMLDeclVersion                        : String -> XMLValue
  XMLDeclEncoding                       : String -> XMLValue
  XMLDeclStandalone                     : Bool -> XMLValue
  XMLDeclComment                        : String -> XMLValue
  XMLDeclProcessingInstruction          : String -> String -> XMLValue
  XMLDocTypeSystem                      : String -> XMLValue
  XMLDocTypePublic                      : String -> String -> XMLValue
  XMLDocTypeComment                     : String -> XMLValue
  XMLDocTypeProcessingInstruction       : String -> String -> XMLValue
  XMLDocTypeInternalSubset              : String -> XMLValue
  XMLElementEmptyTag                    : String -> XMLValue
  XMLElementStartTagName                : String -> XMLValue
  XMLElementStartTagAttributeName       : String -> XMLValue
  XMLElementStartTagAttributeValue      : String -> XMLValue
  XMLElementStartTagNamespceName        : String -> XMLValue
  XMLElementStartTagNamespaceValue      : String -> XMLValue
  XMLElementContentCharData             : String -> XMLValue
  XMLElementContentComment              : String -> XMLValue
  XMLElementContentProcessingIntruction : String -> String -> XMLValue
  XMLElementContentCDATA                : String -> XMLValue
  XMLElementEndTag                      : String -> XMLValue
  XMLMiscComment                        : String -> XMLValue
  XMLMiscProcessingInstruction          : String -> String -> XMLValue

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
  constructor XML
  line      : Ref q Nat
  col       : Ref q Nat
  psns      : Ref q (SnocList Position)
  strs      : Ref q (SnocList String)
  err       : Ref q (Maybe $ BoundedErr Void)
  xmltags   : Ref q (SnocList String)
  xmlvalues : Ref q (SnocList XMLValue)
  xmldoc    : Ref q (SnocList XMLValues)
  bytes     : Ref q ByteString

export %inline
HasPosition XMLSTCK where
  line      = XMLSTCK.line
  col       = XMLSTCK.col
  positions = XMLSTCK.psns

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
  xmlt <- ref1 [<]
  xmlvs <- ref1 [<]
  xmlls <- ref1 [<]
  by <- ref1 ""
  pure (XML l c bs ss er xmlt xmlvs xmlls fc by)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "XMLSz" "XMLST"
  [ "XMLIni"
  , "XMLDeclVersionS"
  , "XMLDeclVersionStrStart"
  , "XMLDeclVersionStr"
  ,""
  , "XMLDeclEncodingStrStart"
  , "XMLDeclStandaloneStrStart"
  , "XMLDeclMiscCommentS"
  , "XMLDeclMiscCommentStrStart"
  , "XMLDeclMiscProcessingInstructionS"
  , "XMLDeclMiscProcessingInstructionStrStart"
  , "XMLEmpty"
  , "XMLComplete"
  ]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

xmlErr : Arr32 XMLSz (XMLSTCK q -> F1 q (BoundedErr Void))
xmlErr =
  arr32 XMLSz (unexpected [])
    [ E XMLBroken $ unexpected ["character other than '>'"]
    , E XMLEmpty $ unexpected ["sequence data"]
    , E XMLHdr $ unexpected ["sequence line"]
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
  xmlvs@(_::_) <- getList x.xmlvalues
    | [] => arrFail XMLSTCK xmlErr XMLEmpty x
  ln <- read1 x.line
  push1 x.xmldoc (MkXMLValues ln xmlvs)
  pure (Right XMLComplete)

xmlInit : DFA q XMLSz XMLSTCK
xmlInit =
  dfa
    [ read (str "<?xml version=") (pure onXMLDeclVersionS)
    , copen (str "<!--") (pure onXMLPrologMiscCommentStr)
    , copen (str "<?") (pure onXMLPrologMiscProcessingInstructionStr)
    , copen '<' (pure onXMLElementStartTagStr)
    ]

xmlDeclVersionS : DFA q XMLSz XMLSTCK
xmlDeclVersionS =
  dfa
    [ copen '"' (pure XMLDeclVersionStrStart)
    ]

xmlDeclVersionStr : DFA q XMLSz XMLSTCK
xmlDeclVersionStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclVersionStrEnd . XMLDeclVersion
    , read (plus $ dot && not '"') (pushStr XMLDeclVersionStr)
    , conv linebreak (const $ pure NL)
    ]

xmlDeclVersionEnd : DFA q XMLSz XMLSTCK
xmlDeclVersionEnd =
  dfa
    [ read (plus ' ') (pure onXMLDeclEncodingStandaloneS)
    ]

xmlDeclEncodingStandalone : DFA q XMLSz XMLSTCK
xmlDeclEncodingStandalone =
  dfa
    [ read (str "encoding=") (pure onXMLDeclEncodingS)
    , read (str "standalone=") (pure onXMLDeclStandaloneS)
    ]

xmlDeclEncodingS : DFA q XMLSz XMLSTCK
xmlDeclEncodingS =
  dfa
    [ copen '"' (pure XMLDeclEncodingStrStart)
    ]

xmlDeclEncodingStr : DFA q XMLSz XMLSTCK
xmlDeclEncodingStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclEncodingStr . XMLDeclEncoding
    , read (plus $ dot && not '"') (pushStr XMLDeclEncodingStr)
    , conv linebreak (const $ pure NL)
    ]

xmlDeclStandaloneS : DFA q XMLSz XMLSTCK
xmlDeclStandaloneS =
  dfa
    [ copen '"' (pure XMLDeclEncodingStrStart)
    ]

xmlDeclStandaloneStr : DFA q XMLSz XMLSTCK
xmlDeclStandaloneStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclStandaloneStr . XMLDeclStandalone
    , read (plus $ dot && not '"') (pushStr XMLDeclStandaloneStr)
    , conv linebreak (const $ pure NL)
    ]

xmlDeclEnd : DFA q XMLSz XMLSTCK
xmlDeclEnd =
  dfa
    [ read (str "?>") (pure XMLDeclComplete)
    ]

xmlPrologMiscCommentStr : DFA q XMLSz XMLSTCK
xmlPrologMiscCommentStr =
  dfa
    [ cclose '-->' $ getStr >>= onXMLDeclStandaloneStr . XMLDeclStandalone
    , read (plus $ dot && not "--") (pushStr XMLDeclStandaloneStr)
    ]

xmlPrologMiscProcessingInstructionStr : DFA q XMLSz XMLSTCK
xmlPrologMiscProcessingInstructionStr =
  dfa
    [ cclose '?>' $ getStr >>= onXMLDeclStandaloneStr . XMLDeclStandalone
    , read (plus $ dot && not "?>") (pushStr XMLDeclStandaloneStr)
    ]

xmlElementStartTagStr : DFA q XMLSz XMLSTCK
xmlElementStartTagStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclVersionStrEnd . XMLDeclVersion
    , read (plus $ dot && not spaceSeparator) (pushStr XMLDeclVersionStr)
    ]

xmlSteps : Lex1 q XMLSz XMLSTCK
xmlSteps =
  lex1
    [ E XMLIni xmlInit
    , E FHdrToNLS fastaHdrStrStart
    , E FHdrToNLR fastaHdrStrRest
    , E FHdrDone fastaFDInit
    , E FDNL fastaFDInit
    , E FD fastaFD
    ]

xmlEOI : XMLST -> XMLSTCK q -> F1 q (Either (BoundedErr Void) XMLDocument)
xmlEOI st x =
  case st == FIni || st == FHdr || st == FEmpty || st == FBroken of
    True  => arrFail XMLSTCK fastaErr st x
    False => T1.do
      _ <- onEOI
      xml <- getList x.xmldoc
      pure (Right xml)

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
