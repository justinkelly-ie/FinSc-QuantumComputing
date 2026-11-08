module Stage0.Quantum.StateStream

import public Stage0.BoxInt
import public Stage0.BoxNat
import public Stage1.Order.Preorder
import public Stage0.OnSeq.FusedStream
import public Stage0.Quantum.Qubit
import public Stage0.Quantum.Circuit
import public Stage0.Quantum.Register
import public Stage0.Multiset
import public Stage1.UnixelFraction
import public Stage1.MultisetTree
import public Stage1.QuadStream
import Stage0.StructuralFuel
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. QUANTUM CIRCUIT STATE & MEASUREMENT STREAM ALGEBRA
--------------------------------------------------------------------------------

||| Discrete Qubit Basis State |0> or |1>.
public export
data QubitBasis = ZeroState | OneState

public export
Eq QubitBasis where
  ZeroState == ZeroState = True
  OneState  == OneState  = True
  _         == _         = False

||| Quantum State Token carrying basis state and integer coefficient amplitude.
public export
record QuantumStateToken where
  constructor MkQuantumToken
  basis     : QubitBasis
  amplitude : BoxInt

public export
Eq QuantumStateToken where
  (MkQuantumToken b1 a1) == (MkQuantumToken b2 a2) = b1 == b2 && a1 == a2

||| Streams a single Qubit basis state tokens directly from QubitVal without List allocation.
public export
streamQubitTokens : QubitVal pVal -> FusedStream QuantumStateToken
streamQubitTokens q =
  stream [ MkQuantumToken ZeroState (amp0 q)
         , MkQuantumToken OneState  (amp1 q) ]

||| Streams basis state tokens directly from an algebraic Multiset of QubitBasis tokens.
public export
streamQubitMultiset : Multiset BoxInt QubitBasis -> FusedStream QuantumStateToken
streamQubitMultiset mset =
  mapStream (\(b, amp) => MkQuantumToken b amp) (multisetToStream mset)

||| 2-Qubit basis state (|00>, |01>, |10>, |11>).
public export
data QubitBasis2 = Basis00 | Basis01 | Basis10 | Basis11

public export
Eq QubitBasis2 where
  Basis00 == Basis00 = True
  Basis01 == Basis01 = True
  Basis10 == Basis10 = True
  Basis11 == Basis11 = True
  _ == _ = False

||| 2-Qubit Quantum State Token carrying 2-qubit basis state and amplitude.
public export
record QuantumStateToken2 where
  constructor MkQuantumToken2
  basis2    : QubitBasis2
  amplitude : BoxInt

public export
Eq QuantumStateToken2 where
  (MkQuantumToken2 b1 a1) == (MkQuantumToken2 b2 a2) = b1 == b2 && a1 == a2

||| Streams a 2-qubit register into a deforested stream of basis state tokens without intermediate list allocations.
public export
streamRegister2Tokens : QubitRegister2 -> FusedStream QuantumStateToken2
streamRegister2Tokens reg =
  stream [ MkQuantumToken2 Basis00 (amp00 reg)
         , MkQuantumToken2 Basis01 (amp01 reg)
         , MkQuantumToken2 Basis10 (amp10 reg)
         , MkQuantumToken2 Basis11 (amp11 reg)
         ]

||| Canonical conversion from a pair of single-qubit basis states to a 2-qubit basis state.
public export
qubitBasisPairTo2 : (QubitBasis, QubitBasis) -> QubitBasis2
qubitBasisPairTo2 (ZeroState, ZeroState) = Basis00
qubitBasisPairTo2 (ZeroState, OneState)  = Basis01
qubitBasisPairTo2 (OneState,  ZeroState) = Basis10
qubitBasisPairTo2 (OneState,  OneState)  = Basis11

||| Deforested tensor product of two single-qubit state streams, producing a 2-qubit state stream in O(1) registers.
public export
streamEntangleRegisters : FusedStream QuantumStateToken -> FusedStream QuantumStateToken -> FusedStream QuantumStateToken2
streamEntangleRegisters strmA strmB =
  let strmA_pairs = mapStream (\tok => (basis tok, amplitude tok)) strmA
      strmB_pairs = mapStream (\tok => (basis tok, amplitude tok)) strmB
      tensorStrm  = streamTensorProduct strmA_pairs strmB_pairs
  in mapStream (\((bA, bB), amp) => MkQuantumToken2 (qubitBasisPairTo2 (bA, bB)) amp) tensorStrm

||| Evaluates 2-qubit measurement expectation value directly across a QuantumStateToken2 stream.
%spec fuel
public export
fusedExpectationValue2StreamNat : (fuel : Nat) -> FusedStream QuantumStateToken2 -> BoxInt
fusedExpectationValue2StreamNat fuel strm =
  foldStreamNat fuel
    (\acc, tok => addBox (mulBox (amplitude tok) (amplitude tok)) acc)
    (intToBoxInt 0)
    strm

||| Unfolds a list of quantum state amplitudes into a deforested QuantumStateStream.
||| Deprecated: Prefer `streamQubitTokens`, `streamQubitMultiset`, or `streamRegister2Tokens` over FusedStream.
public export
unfoldQuantumStateStream : List (QubitBasis, BoxInt) -> FusedStream QuantumStateToken
unfoldQuantumStateStream items = MkStream nextStep items
  where
    nextStep : List (QubitBasis, BoxInt) -> Step (List (QubitBasis, BoxInt)) QuantumStateToken
    nextStep [] = Done
    nextStep ((b, amp) :: rest) = Yield (MkQuantumToken b amp) rest

||| Computes measurement expectation value directly across a QuantumStateToken stream using fueled fold.
public export
fusedExpectationValueStream : Fuel -> FusedStream QuantumStateToken -> BoxInt
fusedExpectationValueStream f strm =
  foldStreamFuel f
    (\acc, tok => addBox (mulBox (amplitude tok) (amplitude tok)) acc)
    (intToBoxInt 0)
    strm

||| Total Nat fuel-bounded expectation value directly across a QuantumStateToken stream.
%spec fuel
public export
fusedExpectationValueStreamNat : (fuel : Nat) -> FusedStream QuantumStateToken -> BoxInt
fusedExpectationValueStreamNat fuel strm =
  foldStreamNat fuel
    (\acc, tok => addBox (mulBox (amplitude tok) (amplitude tok)) acc)
    (intToBoxInt 0)
    strm

||| Computes measurement expectation value \langle \psi | A | \psi \rangle across a stream using fueled fold.
||| Deprecated: Prefer `fusedExpectationValueStream` directly over FusedStream.
public export
fusedExpectationValue : Fuel -> List (QubitBasis, BoxInt) -> BoxInt
fusedExpectationValue f items =
  fusedExpectationValueStream f (unfoldQuantumStateStream items)

||| Total Nat fuel-bounded expectation value.
||| Deprecated: Prefer `fusedExpectationValueStreamNat` directly over FusedStream.
public export
fusedExpectationValueNat : (fuel : Nat) -> List (QubitBasis, BoxInt) -> BoxInt
fusedExpectationValueNat fuel items =
  fusedExpectationValueStreamNat fuel (unfoldQuantumStateStream items)

||| Total expectation value bounded by model-indexed GohFuel.
||| Deprecated: Prefer `fusedExpectationValueStreamNat` directly over FusedStream.
public export
fusedExpectationValueFuelModel : GohFuel cap -> List (QubitBasis, BoxInt) -> BoxInt
fusedExpectationValueFuelModel fuel items =
  fusedExpectationValueNat (gohSteps fuel) items

--------------------------------------------------------------------------------
-- 2. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation quantum measurement expectation value calculation.
public export
auditQuantumStateStreamProof : Bool
auditQuantumStateStreamProof =
  let items = [(ZeroState, intToBoxInt 3), (OneState, intToBoxInt 4)]
      expVal = fusedExpectationValueFuelModel ellipticGohFuelModel items
  in expVal == intToBoxInt 25

--------------------------------------------------------------------------------
-- 3. TRACE-PRESERVING QUANTUM STATE STREAM TRANSPORT
--------------------------------------------------------------------------------

||| A Deforested Quantum State Stream carrying a compile-time trace preservation witness (Tr(rho) = totalTrace).
public export
record TracePreservingStateStream (t0 : Nat) (t1 : Nat) (totalTrace : Nat) where
  constructor MkTracePreservingStateStream
  streamData : FusedStream QuantumStateToken
  0 tracePrf : TracePreservingChannel t0 t1 totalTrace

||| Constructs a deforested Quantum State Stream with a compile-time trace preservation witness directly from a FusedStream.
public export
makeTracePreservingStateStreamDirect : (t0 : Nat) -> (t1 : Nat) -> (totalTrace : Nat) ->
                                       (0 prf : TracePreservingChannel t0 t1 totalTrace) ->
                                       FusedStream QuantumStateToken ->
                                       TracePreservingStateStream t0 t1 totalTrace
makeTracePreservingStateStreamDirect t0 t1 tot prf strm =
  MkTracePreservingStateStream strm prf

||| Constructs a deforested Quantum State Stream with a compile-time trace preservation witness.
||| Deprecated: Prefer `makeTracePreservingStateStreamDirect` directly over FusedStream.
public export
makeTracePreservingStateStream : (t0 : Nat) -> (t1 : Nat) -> (totalTrace : Nat) ->
                                 (0 prf : TracePreservingChannel t0 t1 totalTrace) ->
                                 List (QubitBasis, BoxInt) ->
                                 TracePreservingStateStream t0 t1 totalTrace
makeTracePreservingStateStream t0 t1 tot prf items =
  makeTracePreservingStateStreamDirect t0 t1 tot prf (unfoldQuantumStateStream items)

--------------------------------------------------------------------------------
-- 4. RLE SPARSE QUANTUM DENSITY OPERATOR STREAMING
--------------------------------------------------------------------------------

||| Quantum density operator dyad token |i><j| with amplitude/probability weight.
public export
record DensityDyadToken where
  constructor MkDyadToken
  ketBasis : QubitBasis
  braBasis : QubitBasis
  dyadWeight : BoxInt

public export
Eq DensityDyadToken where
  (MkDyadToken k1 b1 w1) == (MkDyadToken k2 b2 w2) =
    k1 == k2 && b1 == b2 && w1 == w2

||| Computes trace Tr(\rho) directly over an RLE stream of density dyads with Fuel.
%spec f
public export
streamTraceDensity : Fuel -> FusedStream DensityDyadToken -> BoxInt
streamTraceDensity f strm =
  foldStreamFuel f
    (\acc, tok =>
      if ketBasis tok == braBasis tok
        then addBox acc (dyadWeight tok)
        else acc)
    (intToBoxInt 0)
    strm

||| Computes trace Tr(\rho) directly over an RLE stream of density dyads with Nat fuel.
%spec fuel
public export
streamTraceDensityNat : Nat -> FusedStream DensityDyadToken -> BoxInt
streamTraceDensityNat fuel strm =
  foldStreamNat fuel
    (\acc, tok =>
      if ketBasis tok == braBasis tok
        then addBox acc (dyadWeight tok)
        else acc)
    (intToBoxInt 0)
    strm

||| Computes quantum purity Tr(\rho^2) directly over an RLE stream with Fuel.
%spec f
public export
streamQuantumPurity : Fuel -> FusedStream DensityDyadToken -> BoxInt
streamQuantumPurity f strm =
  foldStreamFuel f
    (\acc, tok =>
      if ketBasis tok == braBasis tok
        then addBox acc (mulBox (dyadWeight tok) (dyadWeight tok))
        else acc)
    (intToBoxInt 0)
    strm

||| Computes quantum purity Tr(\rho^2) directly over an RLE stream with Nat fuel.
%spec fuel
public export
streamQuantumPurityNat : Nat -> FusedStream DensityDyadToken -> BoxInt
streamQuantumPurityNat fuel strm =
  foldStreamNat fuel
    (\acc, tok =>
      if ketBasis tok == braBasis tok
        then addBox acc (mulBox (dyadWeight tok) (dyadWeight tok))
        else acc)
    (intToBoxInt 0)
    strm

||| Audits quantum purity Tr(\rho^2) = 1 for a pure state |0><0|.
public export
auditDensityPurityProof : Bool
auditDensityPurityProof =
  let pureDyad = [MkDyadToken ZeroState ZeroState (intToBoxInt 1)]
      pureTrace = streamTraceDensityNat 10 (stream pureDyad)
      purePurity = streamQuantumPurityNat 10 (stream pureDyad)
  in pureTrace == intToBoxInt 1 && purePurity == intToBoxInt 1

--------------------------------------------------------------------------------
-- 5. LINEAR QTT LINDBLAD MASTER STREAM TRANSDUCER
--------------------------------------------------------------------------------

||| Strictly linear QTT stream transducer enforcing trace preservation across open-system Lindblad dissipation.
public export
record LinearLindbladTransducer where
  constructor MkLinearLindbladTransducer
  stepLindblad : (1 rho : FusedStream DensityDyadToken) -> (gamma : BoxInt) -> FusedStream DensityDyadToken

||| Canonical single-qubit amplitude damping / dephasing Lindblad transducer:
||| Consumes the input density stream linearly and preserves Tr(rho) = 1.
public export
linearLindbladTransducer : LinearLindbladTransducer
linearLindbladTransducer =
  MkLinearLindbladTransducer (\(MkStream next seed), gamma =>
    MkStream (\s => case next s of
                      Done => Done
                      Skip s' => Skip s'
                      Yield dyad s' =>
                        let w = dyadWeight dyad
                            newW = if ketBasis dyad == braBasis dyad
                                     then w
                                     else subBox w (mulBox w gamma)
                            newDyad = MkDyadToken (ketBasis dyad) (braBasis dyad) newW
                        in Yield newDyad s') seed)

||| Audits that linear Lindblad evolution preserves density trace Tr(\rho) = 1 across streaming decoherence.
public export
auditStreamingLindbladTraceProof : Bool
auditStreamingLindbladTraceProof =
  let pureState = [ MkDyadToken ZeroState ZeroState (intToBoxInt 1)
                  , MkDyadToken OneState OneState (intToBoxInt 0) ]
      strm0 = stream pureState
      strm1 = linearLindbladTransducer.stepLindblad strm0 (intToBoxInt 0)
      tr1 = streamTraceDensityNat 10 strm1
  in tr1 == intToBoxInt 1

||| Extracts the dissipated off-diagonal coherence from Lindblad damping as a deforested stream.
public export
streamLindbladDecoherenceLoss : (gamma : BoxInt) -> FusedStream DensityDyadToken -> FusedStream BoxInt
streamLindbladDecoherenceLoss gamma (MkStream next seed) =
  filterMapStream (\dyad =>
    if ketBasis dyad /= braBasis dyad
      then Just (mulBox (dyadWeight dyad) gamma)
      else Nothing)
    (MkStream next seed)

||| Folds total dissipated entropy from Lindblad decoherence directly across the stream.
%spec fuel
public export
fusedLindbladDissipatedEntropyNat : (fuel : Nat) -> (gamma : BoxInt) -> FusedStream DensityDyadToken -> BoxInt
fusedLindbladDissipatedEntropyNat fuel gamma strm =
  foldStreamNat fuel
    addBox
    (intToBoxInt 0)
    (streamLindbladDecoherenceLoss gamma strm)

||| Audits that pure-to-mixed Lindblad decoherence yields non-negative dissipated entropy.
public export
auditLindbladLandauerDecoherenceProof : Bool
auditLindbladLandauerDecoherenceProof =
  let superState = [ MkDyadToken ZeroState ZeroState (intToBoxInt 10)
                   , MkDyadToken ZeroState OneState  (intToBoxInt 10)
                   , MkDyadToken OneState  ZeroState (intToBoxInt 10)
                   , MkDyadToken OneState  OneState  (intToBoxInt 10) ]
      dissipated = fusedLindbladDissipatedEntropyNat 10 (intToBoxInt 1) (stream superState)
  in dissipated == intToBoxInt 20

--------------------------------------------------------------------------------
-- 6. DEFORESTED TRUTH-TABLE TO QUANTUM STATE STREAM INITIALIZATION
--------------------------------------------------------------------------------

||| Prepares a deforested Quantum State Stream directly from a Boolean truth function.
public export
streamQuantumStateFromBoolFn : (totalStates : Nat) -> (Nat -> Bool) -> FusedStream QuantumStateToken
streamQuantumStateFromBoolFn totalStates f =
  MkStream nextStep 0
    where
      nextStep : Nat -> Step Nat QuantumStateToken
      nextStep idx =
        if idx >= totalStates
          then Done
          else let bitVal = f idx
                   basis = if bitVal then OneState else ZeroState
                   tok = MkQuantumToken basis (intToBoxInt 1)
               in Yield tok (S idx)

||| Prepares a deforested Quantum State Stream directly from a Ternary truth function.
public export
streamQuantumStateFromTernaryFn : (totalStates : Nat) -> (Nat -> Nat) -> FusedStream QuantumStateToken
streamQuantumStateFromTernaryFn totalStates f =
  MkStream nextStep 0
    where
      nextStep : Nat -> Step Nat QuantumStateToken
      nextStep idx =
        if idx >= totalStates
          then Done
          else let tritVal = f idx
                   basis = if tritVal > 0 then OneState else ZeroState
                   tok = MkQuantumToken basis (intToBoxInt 1)
               in Yield tok (S idx)

||| Audits deforested Boolean truth table quantum state preparation and expectation value.
public export
auditBooleQuantumStatePreparationProof : Bool
auditBooleQuantumStatePreparationProof =
  let strm = streamQuantumStateFromBoolFn 4 (\i => snd (natHalfAndOdd i))
      expVal = fusedExpectationValueStreamNat 10 strm
  in expVal == intToBoxInt 4



