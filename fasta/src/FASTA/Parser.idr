module FASTA.Parser

import Data.Bits
import Data.Buffer
import Data.Linear.Ref1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive

import public Text.ILex

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          HeaderValue
--------------------------------------------------------------------------------

public export
data HeaderValue : Type where
  HNL : HeaderValue
  CAB : String -> HeaderValue
  HV  : String -> HeaderValue

%runElab derive "HeaderValue" [Show,Eq]

--------------------------------------------------------------------------------
--          SequenceValue
--------------------------------------------------------------------------------

public export
data SequenceValue : Type where
  SNL : SequenceValue
  SV  : String -> SequenceValue

%runElab derive "SequenceValue" [Show,Eq]

--------------------------------------------------------------------------------
--          SequenceValues
--------------------------------------------------------------------------------

public export
0 SequenceValues : Type
SequenceValues = List SequenceValue

--------------------------------------------------------------------------------
--          FASTA
--------------------------------------------------------------------------------

public export
record FASTA where
  constructor MkFASTA
  headerline    : List HeaderValue
  sequencelines : List SequenceValues

%runElab derive "FASTA" [Show,Eq]

Interpolation FASTA where interpolate = show

--------------------------------------------------------------------------------
--          RExp
--------------------------------------------------------------------------------

linebreak : RExp True
linebreak = '\n' <|> '\r'

nucleotide : RExp True
nucleotide = 'A' <|> 'T' <|> 'G' <|> 'C'

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

public export
record FSTCK (q : Type) where
  constructor F
  line           : Ref q Nat
  col            : Ref q Nat
  psns           : Ref q (SnocList Position)
  err            : Ref q (Maybe $ BoundedErr Void)
  headervalues   : Ref q (SnocList HeaderValue)
  sequencevalues : Ref q (SnocList SequenceValue)
  sequencelines  : Req q (SnocList SequenceValues)
  bytes          : Ref q ByteString

export %inline
HasPosition FSTCK where
  line      = FSTCK.line
  col       = FSTCK.col
  positions = FSTCK.psns

export %inline
HasError FSTCK Void where
  error = err

export %inline
HasBytes FSTCK where
  bytes = FSTCK.bytes

export
fastainit : F1 q (FSTCK q)
fastainit = T1.do
  l  <- ref1 Z
  c  <- ref1 Z
  bs <- ref1 [<]
  er <- ref1 Nothing
  hvs <- ref1 [<]
  svs <- ref1 [<]
  sls <- ref1 [<]
  by <- ref1 ""
  pure (F l c bs ss er hvs svs sls by)

%runElab deriveParserState "FSz" "FST"
  ["FHIni", "FHCAB", "FHVal", "FHNL", "FHDone", "FSIni", "FSVal", "FSNL", "FSDone"]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFASTAValueFHdr : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFHdr v = push1 x.fastavalues v >> pure FHdr

onFASTAValueFD : (x : FSTCK q) => FASTAValue -> F1 q FST
onFASTAValueFD v = push1 x.fastavalues v >> pure FD

onNL : (x : FSTCK q) => F1 q (Either (BoundedErr Void) FST)
onNL = T1.do
  incline 1
  [] <- getList x.fastavalues
    |
  --fvs@(_::_) <- getList x.fastavalues | [] => pure FIni
  ln <- read1 x.line
  push1 x.fastalines (MkFASTALine ln fvs)
  pure FIni

fastaDflt : DFA q FSz FSTCK
fastaDflt =
  dfa
    [ conv linebreak (\_ => onNL)
    , read ('>' >> plus (dot && not linebreak)) (onFASTAValueFHdr . FHeader)
    , read (plus (nucleotide && not '>' && not linebreak)) (onFASTAValueFD . FData)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FIni fastaDflt
    , E FHdr fastaDflt
    , E FD fastaDflt
    ]

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FNL $ unclosed "\""
    , E FHdr $ unexpected ["no sequence line(s)"]
    , E FD $ unexpected ["^[ATGC]"]
    ]

fastaEOI : FST -> FSTCK q -> F1 q (Either (BoundedErr Void) FASTA)
fastaEOI st x =
  case st == CAB || st == HV of
    True  => arrFail FSTCK fastaErr st x
    False => T1.do
      _     <- onNL
      fasta <- getList x.fastalines
      pure (Right fasta)

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

fasta : P1 q (BoundedErr Void) FSz FSTCK FASTA
fasta = P FIni fastainit fastaSteps snocChunk fastaErr fastaEOI
