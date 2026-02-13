module XML.Parser

import Data.Bits
import Data.Buffer
import Data.ByteString
import Data.Linear.Ref1
import Data.SortedMap
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
--          RExp
--------------------------------------------------------------------------------

whitespace : RExp True
whitespace = ' '

linebreak : RExp True
linebreak = '\n' <|> "\n\r" <|> "\r\n" <|> '\r' <|> '\RS'

--------------------------------------------------------------------------------
--          XMLMiscValue
--------------------------------------------------------------------------------

public export
data XMLMiscValue : Type where
  XMLMiscComment               : String -> XMLMiscValue
  XMLMiscProcessingInstruction : String -> String -> XMLMiscValue

--------------------------------------------------------------------------------
--          XMLDeclValue
--------------------------------------------------------------------------------

public export
data XMLDeclValue : Type where
  XMLDeclVersion    : String -> XMDeclLValue
  XMLDeclEncoding   : String -> XMLDeclValue
  XMLDeclStandalone : Bool -> XMLDeclValue
  XMLDeclNL         : ByteString -> XMLDeclValue
  XMLDeclWhitespace : ByteString -> XMLDeclValue

--------------------------------------------------------------------------------
--          XMLDocTypeValue
--------------------------------------------------------------------------------

public export
data XMLDocTypeValue : Type where
  XMLDocTypeSystem     : String -> XMLDocTypeValue
  XMLDocTypePublic     : String -> String -> XMLDocTypeValue
  XMLDocTypeName       : String -> XMLDocTypeValue
  XMLDocTypeNL         : ByteString -> XMLDocTypeValue
  XMLDocTypeWhitespace : ByteString -> XMLDocTypeValue

--------------------------------------------------------------------------------
--          XMLElementValue
--------------------------------------------------------------------------------

public export
data XMLElementValue : Type where
  XMLElementEmptyTag               : String -> XMLElementValue
  XMLElementStartTagName           : String -> XMLElementValue
  XMLElementStartTagAttributeName  : String -> XMLElementValue
  XMLElementStartTagAttributeValue : String -> XMLElementValue
  XMLElementStartTagNamespaceName  : String -> XMLElementValue
  XMLElementStartTagNamespaceValue : String -> XMLElementValue
  XMLElementCharData               : String -> XMLElementValue
  XMLElementMisc                   : XMLMiscValue -> XMLElementValue
  XMLElementCDATA                  : String -> XMLElementValue
  XMLElementNL                     : ByteString -> XMLElementValue
  XMLElementNode                   : List XMLElementValue -> XMLElementValue

--------------------------------------------------------------------------------
--          XMLDocument
--------------------------------------------------------------------------------

public export
record XMLDocument where
  constructor MkXMLDocument
  decl            : Maybe (List XMLDeclValue)
  postdeclmisc    : Maybe (List Misc)
  doctype         : Maybe (List XMLDocTypeValue)
  postdoctypemisc : Maybe (List Misc)
  root            : List XMLElementValue
  postrootmisc    : Maybe (List Misc)

%runElab derive "XMLDocument" [Show,Eq]

Interpolation XMLDocument where interpolate = show

--------------------------------------------------------------------------------
--          XMLSTCK
--------------------------------------------------------------------------------

public export
record XMLSTCK (q : Type) where
  constructor XML
  line               : Ref q Nat
  col                : Ref q Nat
  psns               : Ref q (SnocList Position)
  strs               : Ref q (SnocList String)
  err                : Ref q (Maybe $ BoundedErr Void)
  xmldecl            : Ref q (SnocList XMLDeclValue)
  xmlpostdeclmisc    : Ref q (SnocList XMLMiscValue)
  xmldoctype         : Ref q (SnocList XMLDocTypeValue)
  xmlpostdoctypemisc : Ref q (SnocList XMLMiscValue)
  xmlrootelement     : Ref q (SnocList XMLElementValue)
  xmlpostrootmisc    : Ref q (SnocList XMLMiscValue)
  xmlelementstack    : Ref q (SnocList (String, SnocList XMLElementValue))
  bytes              : Ref q ByteString

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
  xmldl <- ref1 [<]
  xmlpdl <- ref1 [<]
  xmldt <- ref1 [<]
  xmlpdt <- ref1 [<]
  xmlre <- ref1 [<]
  xmlpre <- ref1 [<]
  es <- ref1 [<]
  by <- ref1 ""
  pure (XML l c bs ss er xmldl xmlpdl xmldt xmlpdt xmlre xmlpre es by)

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

%runElab deriveParserState "XMLSz" "XMLST"
  [ "XMLIni"
  , "XMLEmpty"
  , "XMLComplete"
  , "XMLDeclVersionS"
  , "XMLDeclVersionStrStart"
  , "XMLDeclVersionStr"
  , "XMLDeclVersionE"
  , "XMLDeclVersionPostUnfinished"
  , "XMLDeclEncodingS"
  , "XMLDeclEncodingStrStart"
  , "XMLDeclEncodingStr"
  , "XMLDeclEncodingE"
  , "XMLDeclEncodingPostUnfinished"
  , "XMLDeclStandaloneS"
  , "XMLDeclStandaloneStrStart"
  , "XMLDeclStandaloneStr"
  , "XMLDeclStandaloneE"
  , "XMLDeclMiscCommentStrStart"
  , "XMLDeclMiscCommentStr"
  , "XMLDeclMiscCommentE"
  , "XMLDeclMiscProcessingInstructionStrStart"
  , "XMLDeclMiscProcessingInstructionStr"
  , "XMLDeclMiscProcessingInstructionE"
  , "XMLDeclNLE"
  , "XMLDeclWhitespaceE"
  , "XMLDeclUnfinished"
  , "XMLDeclFinished"
  , "XMLDocTypeSystemS"
  , "XMLDocTypeSystemStrStart"
  , "XMLDocTypeSystemStr"
  , "XMLDocTypeSystemE"
  , "XMLDocTypePublicS"
  , "XMLDocTypePublicStrStart"
  , "XMLDocTypePublicStr"
  , "XMLDocTypePublicE"
  , "XMLDocTypeNameS"
  , "XMLDocTypeNameStrStart"
  , "XMLDocTypeNameStr"
  , "XMLDocTypeNameE"
  , "XMLDocTypeNLE"
  , "XMLDocTypeWhitespaceE"
  , "XMLDocTypeUnfinished"
  , "XMLDoctypeFinished"
  , "XMLElementEmptyTagS"
  , "XMLElementEmptyTagStrStart"
  , "XMLElementEmptyTagStr"
  , "XMLElementEmptyTagE"
  , "XMLElementStartTagNameStrStart"
  , "XMLElementStartTagNameStr"
  , "XMLElementStartTagNameE"
  , "XMLElementStartTagAttributeNameS"
  , "XMLElementStartTagAttributeNameStrStart"
  , "XMLElementStartTagAttributeNameStr"
  , "XMLElementStartTagAttributeNameE"
  , "XMLElementStartTagAttributeValueS"
  , "XMLElementStartTagAttributeValueStrStart"
  , "XMLElementStartTagAttributeValueStr"
  , "XMLElementStartTagAttributeValueE"
  , "XMLElementStartTagNamespaceNameS"
  , "XMLElementStartTagNamespaceNameStrStart"
  , "XMLElementStartTagNamespaceNameStr"
  , "XMLElementStartTagNamespaceNameE"
  , "XMLElementStartTagNamespaceValueS"
  , "XMLElementStartTagNamespaceValueStrStart"
  , "XMLElementStartTagNamespaceValueStr"
  , "XMLElementStartTagNamespaceValueE"
  , "XMLElementCharDataS"
  , "XMLElementCharDataStrStart"
  , "XMLElementCharDataStr"
  , "XMLElementCharDataE"
  , "XMLElementMiscCommentS"
  , "XMLElementMiscCommentStrStart"
  , "XMLElementMiscCommentStr"
  , "XMLElementMiscCommentE"
  , "XMLElementMiscProcessingInstructionS"
  , "XMLElementMiscProcessingInstructionTargetStrStart"
  , "XMLElementMiscProcessingInstructionTargetStr"
  , "XMLElementMiscProcessingInstructionTargetE"
  , "XMLElementMiscProcessingInstructionDataStrStart"
  , "XMLElementMiscProcessingInstructionDataStr"
  , "XMLElementMiscProcessingInstructionDataE"
  , "XMLElementCDATAS"
  , "XMLElementCDATAStrStart"
  , "XMLElementCDATAStr"
  , "XMLElementCDATAE"
  , "XMLElementEndTagS"
  , "XMLElementEndTagStrStart"
  , "XMLElementEndTagStr"
  , "XMLElementEndTagE"
  , "XMLElementFinished"
  , "XMLFinished"
  ]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

xmlErr : Arr32 XMLSz (XMLSTCK q -> F1 q (BoundedErr Void))
xmlErr =
  arr32 XMLSz (unexpected [])
    [ E XMLBroken $ unexpected ["character other than '>'"]
    , E XMLEmpty $ unexpected ["sequence data"]
    ]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onXMLDeclNL : (x : FSTCK q) => ByteString -> F1 q FST
onXMLDeclNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclNLE

onXMLDeclWhitespace : (x : FSTCK q) => ByteString -> F1 q FST
onXMLDeclWhitespace v = incline 1 >> push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclWhitespaceE

onXMLDeclVersionStrEnd : (x : XMLSTCK) => XMLDeclVersion -> F1 q XMLST
onXMLDeclVersionStrEnd v = push1 x.xmldecl v >> pure XMLDeclVersionE

onXMLDeclEncodingStrEnd : (x : XMLSTCK) => XMLDeclEncoding -> F1 q XMLST
onXMLDeclEncodingStrEnd v = push1 x.xmldecl v >> pure XMLDeclEncodingE

onXMLDeclStandaloneStrEnd : (x : XMLSTCK) => XMLDeclStandalone -> F1 q XMLST
onXMLDeclStandaloneStrEnd v = push1 x.xmldecl v >> pure XMLDeclStandaloneE

onXMLDeclMiscCommentStrEnd : (x : XMLSTCK) => XMLDeclMiscComment -> F1 q XMLST
onXMLDeclMiscCommentStrEnd v = push1 x.xmlpostdeclmisc v >> pure XMLDeclMiscCommentE

onXMLDeclMiscProcessingInstructionStrEnd : (x : XMLSTCK) => XMLDeclMiscProcessingInstruction -> F1 q XMLST
onXMLDeclMiscProcessingInstructionStrEnd v = T1.do
  s <- getStr
  let (pitarget, pidata) = break (\x -> x == ' ' || x == '\n' || x == '\r' || x == '\RS') s
      pi = XMLDeclMiscProcessingInstruction pitarget pidata
  push1 x.xmlpostdeclmisc v
  pure XMLDeclMiscProcessingInstructionE

onXMLDocTypeNL : (x : FSTCK q) => ByteString -> F1 q FST
onXMLDoctypeNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeNLE

onXMLDocTypeWhitespace : (x : FSTCK q) => ByteString -> F1 q FST
onXMLDoctypeWhitespace v = incline 1 >> push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeWhitespaceE

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
    [ read (str "<?xml version=") (pure XMLDeclVersionS)
    , copen (str "<!--") (pure XMLDeclMiscCommentS)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionS)
    , copen '<' (pure XMLElementStartTagNameS)
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
    ]

xmlDeclVersionAfter : DFA q XMLSz XMLSTCK
xmlDeclVersionAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclNL bs)
    , conv whitespace (\bs => onXMLDeclWhitespace bs)
    , read (str "?>") (pure XMLDeclFinished)
    ]

xmlDeclVersionPostUnfinished : DFA q XMLSz XMLSTCK
xmlDeclVersionPostUnfinished =
  dfa
    [ read (str "encoding=") (pure XMLDeclEncodingS)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    ]

xmlDeclEncodingS : DFA q XMLSz XMLSTCK
xmlDeclEncodingS =
  dfa
    [ copen '"' (pure XMLDeclEncodingStrStart)
    ]

xmlDeclEncodingStr : DFA q XMLSz XMLSTCK
xmlDeclEncodingStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclEncodingStrEnd . XMLDeclEncoding
    , read (plus $ dot && not '"') (pushStr XMLDeclEncodingStr)
    ]

xmlDeclEncodingAfter : DFA q XMLSz XMLSTCK
xmlDeclEncodingAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclNL bs)
    , conv whitespace (\bs => onXMLDeclWhitespace bs)
    , read (str "?>") (pure XMLDeclFinished)
    ]

xmlDeclEncodingPostUnfinished : DFA q XMLSz XMLSTCK
xmlDeclEncodingPostUnfinished =
  dfa
    [ read (str "standalone=") (pure XMLDeclStandaloneS)
    ]

xmlDeclStandaloneS : DFA q XMLSz XMLSTCK
xmlDeclStandaloneS =
  dfa
    [ copen '"' (pure XMLDeclStandaloneStrStart)
    ]

xmlDeclStandaloneStr : DFA q XMLSz XMLSTCK
xmlDeclStandaloneStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclStandaloneStrEnd . XMLDeclStandalone
    , read (plus $ dot && not '"') (pushStr XMLDeclStandaloneStr)
    ]

xmlDeclStandaloneAfter : DFA q XMLSz XMLSTCK
xmlDeclStandaloneAfter =
  dfa
    [ read (str "?>") (pure XMLDeclFinished)
    ]

xmlPostDecl : DFA q XMLSz XMLSTCK
xmlPostDecl =
  dfa
    [ copen (str "<!--") (pure XMLDeclMiscCommentStrStart)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionStrStart)
    , copen '<' (pure XMLElementStartTagNameStrStart)
    ]

xmlDeclMiscCommentStr : DFA q XMLSz XMLSTCK
xmlDeclMiscCommentStr =
  dfa
    [ cclose "-->" $ getStr >>= onXMLDeclMiscCommentStrEnd . XMLMiscComment
    , read (plus $ dot && not "--") (pushStr XMLDeclStandaloneStr)
    ]

xmlDeclMiscCommentAfter : DFA q XMLSz XMLSTCK
xmlDeclMiscCommentAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclNL bs)
    , conv whitespace (\bs => onXMLDeclWhitespace bs)
    , copen (str "<!-") (pure XMLDeclMiscCommentS)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionS)
    ]

xmlDeclMiscProcessingInstructionStr : DFA q XMLSz XMLSTCK
xmlDeclMiscProcessingInstructionStr =
  dfa
    [ cclose "?>" (\_ => onXMLDeclMiscProcessingInstructionStrEnd)
    , read (plus $ dot && not "?>") (pushStr XMLDeclMiscProcessingInstructionStr)
    ]

xmlDeclMiscProcessingInstructionAfter : DFA q XMLSz XMLSTCK
xmlDeclMiscProcessingInstructionAfter =
  dfa
    [ conv linebreak (\bs => onXMLDeclNL bs)
    , conv whitespace (\bs => onXMLDeclWhitespace bs)
    , copen (str "<!--") (pure XMLDeclMiscCommentStrStart)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionStrStart)
    , copen '<' (pure XMLElementStartTagNameStrStart)
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
    , E XMLDeclVersionS xmlDeclVersionS
    , E XMLDeclVersionStrStart xmlDecVersionStr
    , E XMLDeclVersionE xmlDeclVersionAfter
    , E XMLDeclVersionPostUnfinished xmlDeclVersionPostUnfinished
    , E XMLDeclEncodingS xmlDeclEncodingS
    , E XMLDeclEncodingStrStart xmlDeclEncodingStr
    , E XMLDeclEncodingE xmlDeclEncodingAfter
    , E XMLDeclEncodingPostUnfinished xmlDeclEncodingPostUnfinished
    , E XMLDeclStandaloneS xmlDeclStandaloneS
    , E XMLDeclStandaloneStrStart xmlDeclStandaloneStr
    , E XMLDeclStandaloneE xmlDeclStandaloneAfter
    , E XMLDeclUnfinished xmlDeclVersionPostUnfinished
    , E XMLDeclFinished xmlPostDecl
    ]

xmlEOI : XMLST -> XMLSTCK q -> F1 q (Either (BoundedErr Void) XMLDocument)
xmlEOI st x =
  case st == XMLIni || st == XMLEmpty of
    True  => arrFail XMLSTCK xmlErr st x
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
