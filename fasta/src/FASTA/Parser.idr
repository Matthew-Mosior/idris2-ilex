module FASTA.Parser

import Data.Bits
import Data.Buffer
import Data.Linear.Ref1
import Data.List1
import Derive.Prelude
import Syntax.T1
import Text.ILex.Derive

import public Text.ILex

%default total
%language ElabReflection

%hide BV.unpack
%hide Data.Array.fromList
%hide Data.ByteString.unpack
%hide Data.Linear.(.)
%hide Data.Vect.fromList

--------------------------------------------------------------------------------
--          HeaderValue
--------------------------------------------------------------------------------

public export
data HeaderValue : Type where
  HV  : String -> HeaderValue

%runElab derive "HeaderValue" [Show,Eq]

--------------------------------------------------------------------------------
--          SequenceValue
--------------------------------------------------------------------------------

public export
data SequenceValue : Type where
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
  headerline    : HeaderValue
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
  headerline     : Ref q (Maybe HeaderValue)
  sequencelines  : Ref q (SnocList SequenceValues)
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
  hl <- ref1 Nothing
  sls <- ref1 [<]
  by <- ref1 ""
  pure (F l c bs er hl sls by)

%runElab deriveParserState "FSz" "FST"
  ["FHIni", "FHNC", "FSIni", "FSNC"]

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

fastaErr : Arr32 FSz (FSTCK q -> F1 q (BoundedErr Void))
fastaErr =
  arr32 FSz (unexpected [])
    [ E FHIni $ unexpected ["no header line"]
    , E FHNC $ unexpected ["can't convert to List1"]
    , E FSIni $ unexpected ["no sequence line(s)"]
    , E FSNC $ unexpected ["can't convert to List1"]
    ]

--------------------------------------------------------------------------------
--          State Transitions
--------------------------------------------------------------------------------

onFHL : (x : FSTCK q) => HeaderValue -> F1 q FST
onFHL x v = T1.do
  Just v' <- pure (fromList $ unpack v)
    | Nothing => pure FHNC
  vwithoutnl <- pure (init v')
  push1 x.headerline (Just vwithoutnl)
  incline 1
  pure FSIni

onFSL : (x : FSTCK q) => SequenceValue -> F1 q FST
onFSL x v = T1.do
  Just v' <- pure (fromList $ unpack v)
    | Nothing => pure FSNC
  vwithoutnl <- pure (init v')
  push1 x.sequencelines vwithoutnl
  incline 1
  pure FSIni

fastaDflt : DFA q FSz FSTCK
fastaDflt =
  dfa
    [ read ('>' >> plus (not linebreak) >> linebreak) (onFHL . HV)
    , read (plus (nucleotide && not linebreak) >> linebreak) (onFSL . SV)
    ]

fastaSteps : Lex1 q FSz FSTCK
fastaSteps =
  lex1
    [ E FHIni fastaDflt
    , E FSIni fastaDflt
    ]

fastaEOI : FST -> FSTCK q -> F1 q (Either (BoundedErr Void) FASTA)
fastaEOI st x = T1.do
  Just hdrline <- read1 x.headerline
    | Nothing => arrFail FSTCK fastaErr FHIni x
  seqlines <- getList x.sequencelines
  pure (Right (MkFASTA hdrline seqlines))

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

fasta : P1 q (BoundedErr Void) FSz FSTCK FASTA
fasta = P FHIni fastainit fastaSteps snocChunk fastaErr fastaEOI
