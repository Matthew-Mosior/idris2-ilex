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
  , "XMLDeclVersionNLE"
  , "XMLDeclVersionWhitespaceE"
  , "XMLDeclEncodingS"
  , "XMLDeclEncodingStrStart"
  , "XMLDeclEncodingStr"
  , "XMLDeclEncodingE"
  , "XMLDeclEncodingNLE"
  , "XMLDeclEncodingWhitespaceE"
  , "XMLDeclEncodingPostUnfinished"
  , "XMLDeclStandaloneS"
  , "XMLDeclStandaloneStrStart"
  , "XMLDeclStandaloneStr"
  , "XMLDeclStandaloneE"
  , "XMLDeclStandaloneNLE"
  , "XMLDeclStandaloneWhitespaceE"
  , "XMLDeclMiscCommentStrStart"
  , "XMLDeclMiscCommentStr"
  , "XMLDeclMiscCommentE"
  , "XMLDeclMiscProcessingInstructionStrStart"
  , "XMLDeclMiscProcessingInstructionStr"
  , "XMLDeclMiscProcessingInstructionE"
  , "XMLPostDeclNLE"
  , "XMLPostDeclWhitespaceE"
  , "XMLDeclFinished"
  , "XMLDocTypeNameS"
  , "XMLDocTypeNameStrStart"
  , "XMLDocTypeNameStr"
  , "XMLDocTypeNameE"
  , "XMLDocTypeSystemURIS"
  , "XMLDocTypeSystemURIStrStart"
  , "XMLDocTypeSystemURIStr"
  , "XMLDocTypeSystemURIE"
  , "XMLDocTypePublicPublicIDS"
  , "XMLDocTypePublicPublicIDStrStart"
  , "XMLDocTypePublicPublicIDStr"
  , "XMLDocTypePublicPublicIDE"
  , "XMLDocTypePublicSystemIDS"
  , "XMLDocTypePublicSystemIDStrStart"
  , "XMLDocTypePublicSystemIDStr"
  , "XMLDocTypePublicSystemIDE"
  , "XMLDocTypeBeforeNameNLE"
  , "XMLDocTypeBeforeNameWhitespaceE"
  , "XMLDocTypeAfterNameNLE"
  , "XMLDocTypeAfterNameWhitespaceE"
  , "XMLDocTypeAfterSystemNLE"
  , "XMLDocTypeAfterSystemWhitespaceE"
  , "XMLDocTypeAfterPublicNLE"
  , "XMLDocTypeAfterPublicWhitespaceE"
  , "XMLDocTypeAfterPublicIDNLE"
  , "XMLDocTypeAfterPublicIDWhitespaceE"
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

onXMLDeclPostVersionNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostVersionNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclVersionNLE

onXMLDeclPostVersionWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostVersionWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclVersionWhitespaceE

onXMLDeclPostEncodingNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostEncodingNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclEncodingNLE

onXMLDeclPostEncodingWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostEncodingWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclEncodingWhitespaceE

onXMLDeclPostStandaloneNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostStandaloneNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLDeclStandaloneNLE

onXMLDeclPostStandaloneWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDeclPostStandaloneWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLDeclStandaloneWhitespaceE

onXMLPostDeclNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclNL v = incline 1 >> push1 x.xmldecl (XMLDeclNL v) >> pure XMLPostDeclNLE

onXMLPostDeclWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLPostDeclWhitespace v = push1 x.xmldecl (XMLDeclWhitespace v) >> pure XMLPostDeclWhitespaceE

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

onXMLDocTypeBeforeNameNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeBeforeNameNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeBeforeNameNLE

onXMLDocTypeBeforeNameWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeBeforeNameWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeBeforeNameWhitespaceE

onXMLDocTypeNameStrEnd : (x : XMLSTCK) => XMLDocTypeName -> F1 q XMLST
onXMLDocTypeNameStrEnd v = push1 x.xmldoctype v >> pure XMLDocTypeNameE

onXMLDocTypeAfterNameNL : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterNameNL v = incline 1 >> push1 x.xmldoctype (XMLDocTypeNL v) >> pure XMLDocTypeAfterNameNLE

onXMLDocTypeAfterNameWhitespace : (x : XMLSTCK q) => ByteString -> F1 q XMLST
onXMLDoctypeAfterNameWhitespace v = push1 x.xmldoctype (XMLDocTypeWhitespace v) >> pure XMLDocTypeAfterNameWhitespaceE

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
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
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
    [ conv linebreak (\bs => onXMLDeclPostVersionNL bs)
    , conv whitespace (\bs => onXMLDeclPostVersionWhitespace bs)
    , read (str "encoding=") (pure XMLDeclEncodingS)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLDeclFinished)
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
    [ conv linebreak (\bs => onXMLDeclPostEncodingNL bs)
    , conv whitespace (\bs => onXMLDeclPostEncodingWhitespace bs)
    , read (str "standalone=") (pure XMLDeclStandaloneS)
    , read (str "?>") (pure XMLDeclFinished)
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
    [ conv linebreak (\bs => onXMLDeclPostStandaloneNL bs)
    , conv whitespace (\bs => onXMLDeclPostStandaloneWhitespace bs)
    , read (str "?>") (pure XMLDeclFinished)
    ]

xmlPostDeclStart : DFA q XMLSz XMLSTCK
xmlPostDeclStart =
  dfa
    [ copen (str "<!--") (pure XMLDeclMiscCommentStrStart)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionStrStart)
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
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
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionStrStart)
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , copen '<' (pure XMLElementStartTagNameStrStart)
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
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , copen '<' (pure XMLElementStartTagNameStrStart)
    ]

xmlPostDeclNLAfter : DFA q XMLSz XMLSTCK
xmlPostDeclNLAfter =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclNL bs)
    , conv whitespace (\bs => onXMLPostDeclWhitespace bs)
    , copen (str "<!-") (pure XMLDeclMiscCommentS)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionS)
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , copen '<' (pure XMLElementStartTagNameStrStart)
    ]

xmlPostDeclWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlPostDeclWhitespaceAfter =
  dfa
    [ conv linebreak (\bs => onXMLPostDeclNL bs)
    , conv whitespace (\bs => onXMLPostDeclWhitespace bs)
    , copen (str "<!-") (pure XMLDeclMiscCommentS)
    , copen (str "<?") (pure XMLDeclMiscProcessingInstructionS)
    , copen (str "<!DOCTYPE") (pure XMLDocTypeNameS)
    , copen '<' (pure XMLElementStartTagNameStrStart)
    ]

xmlElementStartTagStr : DFA q XMLSz XMLSTCK
xmlElementStartTagStr =
  dfa
    [ cclose '"' $ getStr >>= onXMLDeclVersionStrEnd . XMLDeclVersion
    , read (plus $ dot && not spaceSeparator) (pushStr XMLDeclVersionStr)
    ]

xmlDocTypeNameS : DFA q XMLSz XMLSTCK
xmlDocTypeNameS =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeNL bs)
    , conv whitespace (\bs => onXMLDocTypeWhitespace bs)
    ]

xmlDocTypeBeforeNameNLAfter : DFA q XMLSz XMLSTCK
xmlDocTypeBeforeNameNLAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeNL bs)
    , conv whitespace (\bs => onXMLDocTypeWhitespace bs)
    , copen dot (pure XMLDocTypeNameStrStart)
    ]

xmlDocTypeBeforeNameWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypeBeforeNameWhitespaceAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforeNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforeNameWhitespace bs)
    , copen dot (pure XMLElementStartTagNameStrStart)
    ]

xmlDocTypeNameStr : DFA q XMLSz XMLSTCK
xmlDocTypeNameStr =
  dfa
    [ cclose linebreak $ getStr >>= onXMLDocTypeNameStrEnd . XMLDocTypeName
    , cclose whitespace $ getStr >>= onXMLDocTypeNameStrEnd . XMLDocTypeName
    , read (plus $ dot && not spaceSeparator) (pushStr XMLDeclVersionStr)
    ]

xmlDocTypeNameAfter : DFA q XMLSz XMLSTCK
xmlDocTypeNameAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeAfterNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeAfterNameWhitespace bs)
    , read '>' (pure XMLDocTypeFinished)
    ]

xmlDocTypeAfterNameNLAfter : DFA q XMLSz XMLSTCK
xmlDocTypeAfterNameNLAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeNL bs)
    , conv whitespace (\bs => onXMLDocTypeWhitespace bs)
    , read "SYSTEM" (pure XMLDocTypeSystemURIS)
    , read "PUBLIC" (pure XMLDocTypePublicPublicIDS)
    ]

xmlDocTypeAfterNameWhitespaceAfter : DFA q XMLSz XMLSTCK
xmlDocTypeAfterNameWhitespaceAfter =
  dfa
    [ conv linebreak (\bs => onXMLDocTypeBeforeNameNL bs)
    , conv whitespace (\bs => onXMLDocTypeBeforeNameWhitespace bs)
    , copen dot (pure XMLElementStartTagNameStrStart)
    ]

xmlSteps : Lex1 q XMLSz XMLSTCK
xmlSteps =
  lex1
    [ E XMLIni xmlInit
    , E XMLDeclVersionS xmlDeclVersionS
    , E XMLDeclVersionStrStart xmlDecVersionStr
    , E XMLDeclVersionNLE xmlDeclVersionAfter
    , E XMLDeclVersionWhitespaceE xmlDeclVersionAfter
    , E XMLDeclVersionE xmlDeclVersionAfter
    , E XMLDeclEncodingS xmlDeclEncodingS
    , E XMLDeclEncodingStrStart xmlDeclEncodingStr
    , E XMLDeclEncodingNLE xmlDeclEncodingAfter
    , E XMLDeclEncodingWhitespaceE xmlDeclEncodingAfter
    , E XMLDeclEncodingE xmlDeclEncodingAfter
    , E XMLDeclStandaloneS xmlDeclStandaloneS
    , E XMLDeclStandaloneStrStart xmlDeclStandaloneStr
    , E XMLDeclStandaloneNLE xmlDeclStandaloneAfter
    , E XMLDeclStandaloneWhitespaceE xmlDeclStandaloneAfter
    , E XMLDeclStandaloneE xmlDeclStandaloneAfter
    , E XMLDeclFinished xmlPostDeclStart
    , E XMLDeclMiscCommentStrStart xmlDeclMiscCommentStr
    , E XMLDeclMiscCommentE xmlDeclMiscCommentAfter
    , E XMLDeclMiscProcessingInstructionStrStart xmlDeclMiscProcessingInstructionStr
    , E XMLDeclMiscProcessingInstructionE xmlDeclMiscProcessingInstructionAfter
    , E XMLPostDeclNLE xmlPostDeclNLAfter
    , E XMLPostDeclWhitespaceE xmlPostDeclWhitespaceAfter
    , E XMLDeclFinished xmlPostDecl
    , E XMLDocTypeNameS xmlDocTypeNameS
    , E XMLDocTypeBeforeNameNLE xmlDocTypeBeforeNameNLAfter
    , E XMLDocTypeBeforeNameWhitespaceE xmlDocTypeBeforeNameWhitespaceAfter
    , E XMLDocTypeNameE xmlDocTypeNameAfter
    , E XMLDocTypeAfterNameNLE xmlDocTypeAfterNameNLAfter
    , E XMLDocTypeAfterNameWhitespaceE xmlDocTypeAfterNameWhitespaceAfter
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
