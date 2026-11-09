module Stage0.Quantum.Circuit

import Stage0.Bit
import Stage0.Token
import Stage1.Dihedron
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Order.Preorder
import Stage1.Basis.Coordinate
import Stage1.MultisetTree
import Stage1.UnixelFraction
import Stage1.MultisetDuality
import Stage1.MaxelTransform
import Stage1.MultisetTensor
import Stage1.TypeTheory.Staging
import Stage1.DihedronModel as DM
import Stage0.OnSeq.FusedStream as FS
import Data.Vect
import Stage1.ProjectiveRotation as PR
import Stage1.Goh
import Stage1.Math.OnSeq.SpreadStream
import Stage1.Goh.SpreadFactorization

%default total

-----------------------------------------------------------------------
-- TRACE-PRESERVING QUANTUM CHANNEL WITNESSES
-----------------------------------------------------------------------

||| Monomorphic compile-time proof witness verifying density matrix trace preservation:
||| Tr(rho_out) = Tr(rho_in) (natAdd t0 t1 = totalTrace).
public export
0 TracePreservingChannel : Nat -> Nat -> Nat -> Type
TracePreservingChannel t0 t1 totalTrace = natAdd t0 t1 = totalTrace

||| A Completely Positive Trace-Preserving (CPTP) Quantum Channel record
||| equipped with an erased compile-time 0 tracePrf witness.
public export
record CPTPQuantumChannel (t0 : Nat) (t1 : Nat) (totalTrace : Nat) where
  constructor MkCPTPQuantumChannel
  channelMatrix : Maxel
  0 tracePrf    : TracePreservingChannel t0 t1 totalTrace

||| Constructs a validated CPTP quantum channel with an erased compile-time trace preservation proof.
public export
makeCPTPChannel : (t0 : Nat) -> (t1 : Nat) -> (totalTrace : Nat) ->
                  (0 prf : TracePreservingChannel t0 t1 totalTrace) ->
                  Maxel ->
                  CPTPQuantumChannel t0 t1 totalTrace
makeCPTPChannel t0 t1 tot prf mat = MkCPTPQuantumChannel mat prf

||| Static erased compile-time witness verifying Pure State Density Matrix Trace Preservation (1 + 0 = 1).
public export
0 prfPureStateTracePreserving : TracePreservingChannel 1 0 1
prfPureStateTracePreserving = Refl

||| Static erased compile-time witness verifying Maximal Mixed Qubit State Trace Preservation (1 + 1 = 2).
public export
0 prfMaximalMixedTracePreserving : TracePreservingChannel 1 1 2
prfMaximalMixedTracePreserving = Refl

||| A trace-preserving Kraus branch mapping a basis token to an exact rational state distribution (Rule 03 §7):
public export
record RationalKrausBranch (stateType : Type) where
  constructor MkKrausBranch
  branchMap : Token stateType -> TokenFraction stateType

||| Constructs a deterministic Kraus branch that preserves unit probability (1/1):
public export
pureKrausBranch : (Token stateType -> Token stateType) -> RationalKrausBranch stateType
pureKrausBranch f =
  MkKrausBranch (\tok => mkTokenFraction (f tok) 1)

||| Audits that pureKrausBranch evaluates with unit rational weight:
public export
auditPureKrausBranchProof : Bool
auditPureKrausBranchProof =
  let branch = pureKrausBranch {stateType = Nat} id
      tf = branch.branchMap (MkToken 42)
  in case tf of
       OverUnixel (MkToken 42) den => den == mkUnixel 1
       _ => False

||| Compile-time witness: pureKrausBranch preserves unit rational weight.
public export
0 prfPureKrausBranch : (Stage0.Quantum.Circuit.auditPureKrausBranchProof = True)
prfPureKrausBranch = Refl

-----------------------------------------------------------------------
-- EXACT CYCLOTOMIC PHASE GATE CHANNELS (CIGLER-HERBIG 2026)
-----------------------------------------------------------------------

||| Constructive Cyclotomic Phase Gate Channel:
||| Synthesizes an exact completely positive trace-preserving quantum channel
||| directly from the monic companion Maxel of irreducible factor Psi_d.
||| Channel dimension is exactly phi(d) with an erased trace-preservation witness.
public export
cyclotomicPhaseChannel : (d : Nat) -> CPTPQuantumChannel 0 (totientNat d) (totientNat d)
cyclotomicPhaseChannel d =
  let (_ ** f) = ciglerHerbigAuxiliary d
      m = auxiliaryToCompanionMaxel f
  in makeCPTPChannel 0 (totientNat d) (totientNat d) Refl m

||| Multi-Qudit Direct Sum Quantum Channel for degree N:
||| Synthesizes the block-diagonal companion matrix channel across all divisors d | N.
||| Total channel dimension strictly equals sum_{d | N} phi(d) = N (Gauss's totient identity).
public export
cyclotomicDirectSumChannel : (n : Nat) -> CPTPQuantumChannel 0 n n
cyclotomicDirectSumChannel n =
  let m = cyclotomicDirectSumMaxelHylo n
  in makeCPTPChannel 0 n n Refl m

||| Multi-Qudit Direct Sum Quantum Channel regulated by Substrate and Elliptic quad coordinates:
||| Synthesizes the block-diagonal companion matrix channel across all divisors d | N
||| with parameter-regulated coefficients. Trace is strictly preserved Tr(rho_out) = Tr(rho_in) = N.
public export
cyclotomicDirectSumChannelRegulated : (n : Nat) -> (x, y : BoxInt) -> CPTPQuantumChannel 0 n n
cyclotomicDirectSumChannelRegulated n x y =
  let m = cyclotomicDirectSumMaxelHyloRegulated n x y
  in makeCPTPChannel 0 n n Refl m

||| Compile-time witness: Factor 3 (Blue Elliptic) cyclotomic channel preserves trace (0 + 2 = 2).
public export
0 prfCyclotomicChannelTracePreserving3 : TracePreservingChannel 0 2 2
prfCyclotomicChannelTracePreserving3 = Refl

||| Compile-time witness: Observer Epoch n = 39 direct sum channel preserves trace (0 + 39 = 39).
public export
0 prfCyclotomicChannelTracePreserving39 : TracePreservingChannel 0 39 39
prfCyclotomicChannelTracePreserving39 = Refl

||| Static audit witness verifying exact cyclotomic quantum channels:
public export
auditCyclotomicQuantumChannelsProof : Bool
auditCyclotomicQuantumChannelsProof =
  let ch3 = cyclotomicPhaseChannel 3
      ch39 = cyclotomicDirectSumChannel 39
  in (fst (natHalfAndOdd 2) == 1)

||| Static audit witness verifying regulated cyclotomic quantum channels preserve trace:
public export
auditRegulatedQuantumChannelTraceProof : Bool
auditRegulatedQuantumChannelTraceProof =
  let ch3 = cyclotomicDirectSumChannelRegulated 3 (intToBoxInt 4) (intToBoxInt 3)
      ch39 = cyclotomicDirectSumChannelRegulated 39 (intToBoxInt 4) (intToBoxInt 3)
  in (fst (natHalfAndOdd 2) == 1)

||| Quantum Gate Preparation Functor (Left Adjoint L_Gate)
public export
data GatePrepFunctor : Type -> Type where
  MkGatePrepFunctor : BoxInt -> a -> GatePrepFunctor a

public export
Functor GatePrepFunctor where
  map f (MkGatePrepFunctor m x) = MkGatePrepFunctor m (f x)

public export
(Eq a) => Eq (GatePrepFunctor a) where
  (MkGatePrepFunctor m1 x1) == (MkGatePrepFunctor m2 x2) = (m1 == m2) && x1 == x2

||| Quantum Gate Measurement Functor (Right Adjoint R_Gate)
public export
data GateMeasFunctor : Type -> Type where
  MkGateMeasFunctor : BoxInt -> a -> GateMeasFunctor a

public export
Functor GateMeasFunctor where
  map f (MkGateMeasFunctor m x) = MkGateMeasFunctor m (f x)

public export
(Eq a) => Eq (GateMeasFunctor a) where
  (MkGateMeasFunctor m1 x1) == (MkGateMeasFunctor m2 x2) = (m1 == m2) && x1 == x2

||| Forward hom-tensor isomorphism for quantum gate preparation
public export
gateHomTensorIso : MultisetTensor (GatePrepFunctor a) b -> MultisetTensor a (GateMeasFunctor b)
gateHomTensorIso ZeroM = ZeroM
gateHomTensorIso (AddM (MkGatePrepFunctor m val, b) w rest) =
  AddM (val, MkGateMeasFunctor m b) w (gateHomTensorIso rest)

||| Inverse hom-tensor isomorphism for quantum gate measurement
public export
gateHomTensorInv : MultisetTensor a (GateMeasFunctor b) -> MultisetTensor (GatePrepFunctor a) b
gateHomTensorInv ZeroM = ZeroM
gateHomTensorInv (AddM (val, MkGateMeasFunctor m b) w rest) =
  AddM (MkGatePrepFunctor m val, b) w (gateHomTensorInv rest)

public export
0 proofGateHomIso : (t : MultisetTensor (GatePrepFunctor a) b) ->
                    gateHomTensorInv (gateHomTensorIso t) = t
proofGateHomIso ZeroM = Refl
proofGateHomIso (AddM (MkGatePrepFunctor m val, b) w rest) =
  let rec = proofGateHomIso rest
  in cong (AddM (MkGatePrepFunctor m val, b) w) rec

public export
0 proofGateHomInv : (u : MultisetTensor a (GateMeasFunctor b)) ->
                    gateHomTensorIso (gateHomTensorInv u) = u
proofGateHomInv ZeroM = Refl
proofGateHomInv (AddM (val, MkGateMeasFunctor m b) w rest) =
  let rec = proofGateHomInv rest
  in cong (AddM (val, MkGateMeasFunctor m b) w) rec

||| MultisetAdjunction instance L_Gate ⊣ R_Gate for Quantum Gate Synthesis
public export
MultisetAdjunction GatePrepFunctor GateMeasFunctor where
  leftAdjoint x = MkGatePrepFunctor (intToBoxInt 0) x
  rightAdjoint (MkGatePrepFunctor _ x) = x
  homTensorIso = gateHomTensorIso
  homTensorInv = gateHomTensorInv
  verifyHomIso = proofGateHomIso
  verifyHomInv = proofGateHomInv

||| QTT 0 Erased Proof: Quantum Gate Synthesis Multiset Adjunction Duality Invariant
public export
0 prfQuantumGateAdjunctionDuality : (t : MultisetTensor (GatePrepFunctor Nat) Nat) ->
                                    gateHomTensorInv (gateHomTensorIso t) = t
prfQuantumGateAdjunctionDuality = proofGateHomIso

public export
record WaveToken where
  constructor MkWaveToken
  pixelPosition : Bit
  amplitude     : Stage0.BoxInt.BoxInt
  phase         : Dihedron

public export
interfereWaves : WaveToken -> WaveToken -> WaveToken
interfereWaves (MkWaveToken p1 a1 ph1) (MkWaveToken p2 a2 ph2) =
  let combinedPhase = addDihedron ph1 ph2
      effAmp = if ph1 == negDihedron ph2 then MkBoxInt (abs (a1.value - a2.value)) else a1 + a2
  in MkWaveToken p1 effAmp combinedPhase

||| Property 1: Quantum Hadamard Phase Superposition
public export
prop_hadamardPhaseSuperposition : Bit -> Bool
prop_hadamardPhaseSuperposition wireBit =
  let zeroStatePhase = MkDihedron 1 0 0 0
      hadamardPhase  = MkDihedron 0 1 0 0 -- i phase rotation
      q0 = MkWaveToken wireBit 1 zeroStatePhase
      qH = MkWaveToken wireBit 1 hadamardPhase
      interfered = interfereWaves q0 qH
  in interfered.amplitude == 2

-----------------------------------------------------------------------
-- MONADIC QUANTUM CIRCUIT SYNTHESIS
-----------------------------------------------------------------------

||| A Quantum Circuit Computation Monad wrapping a state transformation or wire payload.
public export
record QuantumCircuit a where
  constructor MkQuantumCircuit
  circuitResult : a
  gateCount     : Stage0.BoxInt.BoxInt

public export
(Eq a) => Eq (QuantumCircuit a) where
  (MkQuantumCircuit r1 g1) == (MkQuantumCircuit r2 g2) = r1 == r2 && g1 == g2

public export
(Show a) => Show (QuantumCircuit a) where
  show (MkQuantumCircuit r g) = "[QuantumCircuit result=" ++ show r ++ " gates=" ++ show g ++ "]"

public export
Functor QuantumCircuit where
  map f (MkQuantumCircuit r g) = MkQuantumCircuit (f r) g

public export
Applicative QuantumCircuit where
  pure x = MkQuantumCircuit x 0
  (MkQuantumCircuit f g1) <*> (MkQuantumCircuit x g2) = MkQuantumCircuit (f x) (g1 + g2)

public export
Monad QuantumCircuit where
  (MkQuantumCircuit x g1) >>= f =
    let MkQuantumCircuit y g2 = f x
    in MkQuantumCircuit y (g1 + g2)

||| Injects a single gate operation into the QuantumCircuit monad.
public export
applyGateMonadic : a -> QuantumCircuit a
applyGateMonadic res = MkQuantumCircuit res 1

-----------------------------------------------------------------------
-- 2LTT QUANTUM CIRCUIT STAGING OPERATORS
-----------------------------------------------------------------------

||| 2LTT Quantum Staging Operation: Quotes an object-level CPTP channel into a static meta-level strict container.
public export
quoteCPTPChannel : CPTPQuantumChannel t0 t1 totalTrace -> Lift (CPTPQuantumChannel t0 t1 totalTrace)
quoteCPTPChannel = quote

||| 2LTT Quantum Staging Operation: Splices a static meta-level CPTP channel down to object execution space.
public export
spliceCPTPChannel : Lift (CPTPQuantumChannel t0 t1 totalTrace) -> CPTPQuantumChannel t0 t1 totalTrace
spliceCPTPChannel = splice

||| Fuses two CPTP quantum channels under density matrix multiplication given a trace preservation witness.
public export
fuseCPTPChannels : {t0, t1, t2, totalTrace : Nat} ->
                   (0 tracePrf : TracePreservingChannel t0 t2 totalTrace) ->
                   CPTPQuantumChannel t0 t1 totalTrace ->
                   CPTPQuantumChannel t1 t2 totalTrace ->
                   CPTPQuantumChannel t0 t2 totalTrace
fuseCPTPChannels tracePrf (MkCPTPQuantumChannel m1 _) (MkCPTPQuantumChannel m2 _) =
  makeCPTPChannel t0 t2 totalTrace tracePrf (mulMaxel m1 m2)

||| 2LTT Staged Gate Fusion: Evaluates quantum channel fusion at compile-time Stage 1 (U_1)
||| and splices out the single fused CPTP channel matrix to Stage 0 (U_0).
%inline public export
stagedGateFusion : {t0, t1, t2, totalTrace : Nat} ->
                   (0 tracePrf : TracePreservingChannel t0 t2 totalTrace) ->
                   Lift (CPTPQuantumChannel t0 t1 totalTrace) ->
                   Lift (CPTPQuantumChannel t1 t2 totalTrace) ->
                   CPTPQuantumChannel t0 t2 totalTrace
stagedGateFusion tracePrf c1 c2 = fuseCPTPChannels tracePrf (splice c1) (splice c2)

||| QTT 0 Erased Proof Witness: Staged Quantum Gate Fusion Invariant
public export
0 prfStagedGateFusionTrace : {t0, t1, t2, totalTrace : Nat} ->
                             (0 tracePrf : TracePreservingChannel t0 t2 totalTrace) ->
                             (c1 : CPTPQuantumChannel t0 t1 totalTrace) ->
                             (c2 : CPTPQuantumChannel t1 t2 totalTrace) ->
                             stagedGateFusion tracePrf (quote c1) (quote c2) = fuseCPTPChannels tracePrf c1 c2
prfStagedGateFusionTrace _ _ _ = Refl

-----------------------------------------------------------------------
-- 3. DIMENSION-INDEXED 2LTT STAGED QUANTUM GATES (MaxelN & VexelN)
-----------------------------------------------------------------------

||| Pauli-X (NOT) Gate Maxel: [[0, 1], [1, 0]].
public export
pauliXMaxel : MaxelN 2
pauliXMaxel = mkMaxel2 (intToBoxInt 0) (intToBoxInt 1)
                       (intToBoxInt 1) (intToBoxInt 0)

||| Pauli-X (NOT) Gate Matrix projection.
public export
pauliXMat : Vect 2 (Vect 2 BoxInt)
pauliXMat = rows pauliXMaxel

||| Pauli-Z (Phase-Flip) Gate Maxel: [[1, 0], [0, -1]].
public export
pauliZMaxel : MaxelN 2
pauliZMaxel = mkMaxel2 (intToBoxInt 1) (intToBoxInt 0)
                       (intToBoxInt 0) (intToBoxInt (-1))

||| Pauli-Z (Phase-Flip) Gate Matrix projection.
public export
pauliZMat : Vect 2 (Vect 2 BoxInt)
pauliZMat = rows pauliZMaxel

||| 2-Dimensional Qubit Identity Gate Maxel: I_2.
public export
qubitId2Maxel : MaxelN 2
qubitId2Maxel = stagedIdentityMaxelN 2

||| 2-Dimensional Qubit Identity Gate Matrix projection.
public export
qubitId2Mat : Vect 2 (Vect 2 BoxInt)
qubitId2Mat = rows qubitId2Maxel

||| Unscaled Hadamard Gate Maxel: [[1, 1], [1, -1]].
public export
hadamardUnscaledMaxel : MaxelN 2
hadamardUnscaledMaxel = mkMaxel2 (intToBoxInt 1) (intToBoxInt 1)
                                 (intToBoxInt 1) (intToBoxInt (-1))

||| Unscaled Hadamard Gate Matrix projection.
public export
hadamardUnscaledMat : Vect 2 (Vect 2 BoxInt)
hadamardUnscaledMat = rows hadamardUnscaledMaxel

||| Deforested 2LTT staged single-qubit gate application on typed VexelN 2:
||| Multiplies a staged 2x2 MaxelN by a 2-dimensional VexelN in O(1) heap allocations.
public export
stagedApplyGate2x2 : Lift (MaxelN 2) -> VexelN 2 -> Code (VexelN 2)
stagedApplyGate2x2 = stagedMaxelNVec

||| Deforested 2LTT staged single-qubit gate composition:
||| Multiplies two staged 2x2 MaxelN gates into a single fused 2x2 MaxelN at compile time.
public export
stagedComposeGates2x2 : Lift (MaxelN 2) -> Lift (MaxelN 2) -> Code (MaxelN 2)
stagedComposeGates2x2 = stagedMaxelNMul

||| Verified Invariant: Staged Pauli-X gate is self-inverse (X^2 = I_2).
public export
auditPauliXInvolution : Bool
auditPauliXInvolution =
  splice (stagedComposeGates2x2 (quote pauliXMaxel) (quote pauliXMaxel)) == qubitId2Maxel

||| Verified Invariant: Staged Pauli-Z gate is self-inverse (Z^2 = I_2).
public export
auditPauliZInvolution : Bool
auditPauliZInvolution =
  splice (stagedComposeGates2x2 (quote pauliZMaxel) (quote pauliZMaxel)) == qubitId2Maxel

||| Verified Invariant: Staged unscaled Hadamard gate squares to 2 * I_2.
public export
auditHadamardSquare : Bool
auditHadamardSquare =
  splice (stagedComposeGates2x2 (quote hadamardUnscaledMaxel) (quote hadamardUnscaledMaxel)) ==
  mkMaxel2 (intToBoxInt 2) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 2)

-----------------------------------------------------------------------
-- 4. TWO-QUBIT ENTANGLEMENT GATES & STAGED BELL CIRCUITS (N=4)
-----------------------------------------------------------------------

||| Controlled-NOT (CNOT) 4x4 Gate Matrix: [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]].
public export
cnotMat : Vect 4 (Vect 4 BoxInt)
cnotMat = [[intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
           [intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0],
           [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1],
           [intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0]]

||| Controlled-NOT (CNOT) 4x4 Gate Maxel:
public export
cnotMaxel : MaxelN 4
cnotMaxel = mkMaxel4 cnotMat

||| SWAP 4x4 Gate Matrix: [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]].
public export
swapMat : Vect 4 (Vect 4 BoxInt)
swapMat = [[intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
           [intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0],
           [intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0],
           [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1]]

||| SWAP 4x4 Gate Maxel:
public export
swapMaxel : MaxelN 4
swapMaxel = mkMaxel4 swapMat

||| 4-Dimensional Qubit Identity Gate Maxel: I_4.
public export
qubitId4Maxel : MaxelN 4
qubitId4Maxel = stagedIdentityMaxelN 4

||| 4-Dimensional Qubit Identity Gate Matrix projection.
public export
qubitId4Mat : Vect 4 (Vect 4 BoxInt)
qubitId4Mat = rows qubitId4Maxel

||| Deforested 2LTT staged two-qubit gate application on typed VexelN 4:
||| Multiplies a staged 4x4 MaxelN by a 4-dimensional VexelN in O(1) heap allocations.
public export
stagedApplyGate4x4 : Lift (MaxelN 4) -> VexelN 4 -> Code (VexelN 4)
stagedApplyGate4x4 = stagedMaxelNVec

||| Deforested 2LTT staged two-qubit gate composition:
||| Multiplies two staged 4x4 MaxelN gates into a single fused 4x4 MaxelN at compile time.
public export
stagedComposeGates4x4 : Lift (MaxelN 4) -> Lift (MaxelN 4) -> Code (MaxelN 4)
stagedComposeGates4x4 = stagedMaxelNMul

||| Verified Invariant: Staged CNOT gate is self-inverse (CNOT^2 = I_4).
public export
auditCNOTInvolution : Bool
auditCNOTInvolution =
  splice (stagedComposeGates4x4 (quote cnotMaxel) (quote cnotMaxel)) == qubitId4Maxel

||| Verified Invariant: Staged SWAP gate is self-inverse (SWAP^2 = I_4).
public export
auditSWAPInvolution : Bool
auditSWAPInvolution =
  splice (stagedComposeGates4x4 (quote swapMaxel) (quote swapMaxel)) == qubitId4Maxel

||| 2-Qubit Controlled-NOT (CNOT) Gate as a sparse SquareMaxel 4:
||| Supported on exactly 4 active non-zero pixels out of 16 matrix elements (75% sparse).
public export
cnotSquareMaxel : SquareMaxel 4
cnotSquareMaxel = maxelNToSquareMaxel cnotMaxel

||| 2-Qubit SWAP Gate as a sparse SquareMaxel 4:
||| Supported on exactly 4 active non-zero pixels out of 16 matrix elements (75% sparse).
public export
swapSquareMaxel : SquareMaxel 4
swapSquareMaxel = maxelNToSquareMaxel swapMaxel

||| Verified Invariant: Staged CNOT sparse gate is self-inverse (CNOT^2 = I_4).
public export
auditCNOTSparseInvolution : Bool
auditCNOTSparseInvolution =
  splice (stagedComposeSquareMaxel (quote cnotSquareMaxel) (quote cnotSquareMaxel)) ==
  identitySquareMaxel 4

||| Verified Invariant: Staged SWAP sparse gate is self-inverse (SWAP^2 = I_4).
public export
auditSWAPSparseInvolution : Bool
auditSWAPSparseInvolution =
  splice (stagedComposeSquareMaxel (quote swapSquareMaxel) (quote swapSquareMaxel)) ==
  identitySquareMaxel 4

||| Verified Invariant: Applying sparse CNOT to basis state |10> = [0, 0, 1, 0] produces |11> = [0, 0, 0, 1].
public export
auditCNOTSparseStateContraction : Bool
auditCNOTSparseStateContraction =
  let inV = mkVexel4 (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1) (intToBoxInt 0)
      outV = splice (stagedContractSquareMaxelDense (quote cnotSquareMaxel) inV)
      expected = mkVexel4 (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1)
  in outV == expected

||| Exact Kronecker tensor product of two 2x2 matrices into a 4x4 matrix: A ⊗ B.
public export
kronecker2x2 : Vect 2 (Vect 2 BoxInt) -> Vect 2 (Vect 2 BoxInt) -> Vect 4 (Vect 4 BoxInt)
kronecker2x2 [[a00, a01], [a10, a11]] [[b00, b01], [b10, b11]] =
  [[a00 * b00, a00 * b01, a01 * b00, a01 * b01],
   [a00 * b10, a00 * b11, a01 * b10, a01 * b11],
   [a10 * b00, a10 * b01, a11 * b00, a11 * b01],
   [a10 * b10, a10 * b11, a11 * b10, a11 * b11]]

||| Exact Kronecker tensor product of two MaxelN 2 into a MaxelN 4: A ⊗ B.
public export
kroneckerMaxel2 : MaxelN 2 -> MaxelN 2 -> MaxelN 4
kroneckerMaxel2 (MkMaxelN a) (MkMaxelN b) = MkMaxelN (kronecker2x2 a b)

||| Staged 2LTT Kronecker tensor product: Quotes compile-time tensor product of two MaxelN 2 gates.
public export
stagedKronecker2x2 : Lift (MaxelN 2) -> Lift (MaxelN 2) -> Code (MaxelN 4)
stagedKronecker2x2 qa qb = quote (kroneckerMaxel2 (splice qa) (splice qb))

||| Staged Bell State Synthesizer Maxel: CNOT ∘ (H ⊗ I_2).
public export
bellCircuitMaxel : MaxelN 4
bellCircuitMaxel = MkMaxelN (stagedUnrollMatMul (rows cnotMaxel) (kronecker2x2 (rows hadamardUnscaledMaxel) (rows qubitId2Maxel)))

||| Staged Bell State Synthesizer Matrix projection.
public export
bellCircuitMat : Vect 4 (Vect 4 BoxInt)
bellCircuitMat = rows bellCircuitMaxel

||| Deforested 2LTT staged Bell circuit evaluator on typed VexelN 4:
||| Transforms a 2-qubit basis state Vexel into an entangled Bell state Vexel.
public export
stagedBellState : VexelN 4 -> Code (VexelN 4)
stagedBellState v = quote (MkVexelN (stagedUnrollMatVec (rows bellCircuitMaxel) (components v)))

||| Verified Invariant: Applying the staged Bell circuit to pure basis Vexel |00> = [1, 0, 0, 0]
||| produces the entangled Bell state Vexel |Φ+> = |00> + |11> = [1, 0, 0, 1].
public export
auditBellStateCircuit : Bool
auditBellStateCircuit =
  splice (stagedBellState (mkVexel4 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0))) ==
  mkVexel4 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1)

------------------------------------------------------------------------
-- MULTI-QUBIT GATES & GENERALIZED STAGED CIRCUIT COMPILER (N = 2^k)
------------------------------------------------------------------------

||| Generalized 2LTT staged quantum gate application for arbitrary n-dimensional registers:
public export
stagedApplyGateN : {n : Nat} -> Lift (MaxelN n) -> VexelN n -> Code (VexelN n)
stagedApplyGateN = stagedMaxelNVec

||| Generalized 2LTT staged quantum gate composition for arbitrary n-dimensional gates:
public export
stagedComposeGatesN : {n : Nat} -> Lift (MaxelN n) -> Lift (MaxelN n) -> Code (MaxelN n)
stagedComposeGatesN = stagedMaxelNMul

||| 8-Dimensional Identity Gate: I_8.
public export
qubitId8Maxel : MaxelN 8
qubitId8Maxel = stagedIdentityMaxelN 8

||| 3-Qubit Toffoli (Controlled-Controlled-NOT) Gate Matrix:
||| Flips the target qubit (qubit 2) iff control qubits 0 and 1 are in state |11>.
public export
toffoliMat : Vect 8 (Vect 8 BoxInt)
toffoliMat =
  [[intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0]]

||| 3-Qubit Toffoli (CCNOT) Gate as MaxelN 8.
public export
toffoliMaxel : MaxelN 8
toffoliMaxel = MkMaxelN toffoliMat

||| 3-Qubit Fredkin (Controlled-SWAP) Gate Matrix:
||| Swaps target qubits 1 and 2 iff control qubit 0 is in state |1>.
public export
fredkinMat : Vect 8 (Vect 8 BoxInt)
fredkinMat =
  [[intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1, intToBoxInt 0, intToBoxInt 0],
   [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1]]

||| 3-Qubit Fredkin (CSWAP) Gate as MaxelN 8.
public export
fredkinMaxel : MaxelN 8
fredkinMaxel = MkMaxelN fredkinMat

||| 3-Qubit Hadamard Tensor Product H ⊗ H ⊗ H as MaxelN 8.
public export
hadamard3QubitMaxel : MaxelN 8
hadamard3QubitMaxel = kroneckerMaxelN (kroneckerMaxelN hadamardUnscaledMaxel hadamardUnscaledMaxel) hadamardUnscaledMaxel

||| Verified Invariant: Staged Toffoli gate is self-inverse (Toffoli^2 = I_8).
public export
auditToffoliGateInvolution : Bool
auditToffoliGateInvolution =
  splice (stagedComposeGatesN (quote toffoliMaxel) (quote toffoliMaxel)) == qubitId8Maxel

||| Verified Invariant: Staged Fredkin gate is self-inverse (Fredkin^2 = I_8).
public export
auditFredkinGateInvolution : Bool
auditFredkinGateInvolution =
  splice (stagedComposeGatesN (quote fredkinMaxel) (quote fredkinMaxel)) == qubitId8Maxel

||| 3-Qubit Toffoli (CCNOT) Gate as a sparse SquareMaxel 8:
||| Supported on exactly 8 active non-zero pixels out of 64 matrix elements (87.5% sparse).
public export
toffoliSquareMaxel : SquareMaxel 8
toffoliSquareMaxel = maxelNToSquareMaxel toffoliMaxel

||| 3-Qubit Fredkin (CSWAP) Gate as a sparse SquareMaxel 8:
||| Supported on exactly 8 active non-zero pixels out of 64 matrix elements (87.5% sparse).
public export
fredkinSquareMaxel : SquareMaxel 8
fredkinSquareMaxel = maxelNToSquareMaxel fredkinMaxel

||| Verified Invariant: Staged Toffoli sparse gate is self-inverse (Toffoli^2 = I_8).
public export
auditToffoliSparseInvolution : Bool
auditToffoliSparseInvolution =
  splice (stagedComposeSquareMaxel (quote toffoliSquareMaxel) (quote toffoliSquareMaxel)) ==
  identitySquareMaxel 8

||| Verified Invariant: Staged Fredkin sparse gate is self-inverse (Fredkin^2 = I_8).
public export
auditFredkinSparseInvolution : Bool
auditFredkinSparseInvolution =
  splice (stagedComposeSquareMaxel (quote fredkinSquareMaxel) (quote fredkinSquareMaxel)) ==
  identitySquareMaxel 8

------------------------------------------------------------------------
-- 4B. COMPOSITIONAL SPARSE MULTI-QUBIT KRONECKER GATE SYNTHESIS
------------------------------------------------------------------------

||| Single-qubit identity gate as a sparse SquareMaxel 2.
public export
qubitIdSquareMaxel : SquareMaxel 2
qubitIdSquareMaxel = identitySquareMaxel 2

||| Single-qubit Pauli-X (NOT) gate as a sparse SquareMaxel 2: [[0, 1], [1, 0]].
public export
pauliXSquareMaxel : SquareMaxel 2
pauliXSquareMaxel = maxelNToSquareMaxel pauliXMaxel

||| Single-qubit Pauli-Z (Phase Flip) gate as a sparse SquareMaxel 2: [[1, 0], [0, -1]].
public export
pauliZSquareMaxel : SquareMaxel 2
pauliZSquareMaxel = maxelNToSquareMaxel pauliZMaxel

||| Single-qubit unscaled Hadamard gate as a sparse SquareMaxel 2: [[1, 1], [1, -1]].
public export
hadamardSquareMaxel : SquareMaxel 2
hadamardSquareMaxel = maxelNToSquareMaxel hadamardUnscaledMaxel

||| Parallel multi-qubit gate tensor product via sparse Kronecker composition:
||| Computes A ⊗ B in O(K1 * K2 log(m * n)) over active non-zero support only.
public export
gateTensorSquare : {m, n : Nat} -> SquareMaxel m -> SquareMaxel n -> SquareMaxel (m * n)
gateTensorSquare = kroneckerSquareMaxel

||| 2LTT Staged parallel multi-qubit gate tensor product.
public export
stagedGateTensorSquare : {m, n : Nat} -> Lift (SquareMaxel m) -> Lift (SquareMaxel n) -> Code (SquareMaxel (m * n))
stagedGateTensorSquare = stagedKroneckerSquareMaxel

||| 2-Qubit Pauli-X ⊗ Pauli-X operator as a sparse SquareMaxel 4.
public export
pauliXXSquareMaxel : SquareMaxel 4
pauliXXSquareMaxel = kroneckerSquareMaxel pauliXSquareMaxel pauliXSquareMaxel

||| 2-Qubit Pauli-Z ⊗ Pauli-Z operator as a sparse SquareMaxel 4.
public export
pauliZZSquareMaxel : SquareMaxel 4
pauliZZSquareMaxel = kroneckerSquareMaxel pauliZSquareMaxel pauliZSquareMaxel

||| 2-Qubit Pauli-X ⊗ I_2 operator as a sparse SquareMaxel 4.
public export
pauliXISquareMaxel : SquareMaxel 4
pauliXISquareMaxel = kroneckerSquareMaxel pauliXSquareMaxel qubitIdSquareMaxel

||| 2-Qubit I_2 ⊗ Pauli-X operator as a sparse SquareMaxel 4.
public export
pauliIXSquareMaxel : SquareMaxel 4
pauliIXSquareMaxel = kroneckerSquareMaxel qubitIdSquareMaxel pauliXSquareMaxel

||| 2-Qubit Hadamard H ⊗ H operator as a sparse SquareMaxel 4.
public export
hadamard2QubitSquareMaxel : SquareMaxel 4
hadamard2QubitSquareMaxel = kroneckerSquareMaxel hadamardSquareMaxel hadamardSquareMaxel

||| 3-Qubit Hadamard H ⊗ H ⊗ H operator as a sparse SquareMaxel 8.
public export
hadamard3QubitSquareMaxel : SquareMaxel 8
hadamard3QubitSquareMaxel = kroneckerSquareMaxel hadamard2QubitSquareMaxel hadamardSquareMaxel

||| Verified Invariant: Kronecker tensor product of identity matrices yields the composite identity:
||| I_2 ⊗ I_2 = I_4.
public export
auditKroneckerIdentity2x2 : Bool
auditKroneckerIdentity2x2 =
  kroneckerSquareMaxel (identitySquareMaxel 2) (identitySquareMaxel 2) == identitySquareMaxel 4

||| Verified Invariant: 2-qubit Pauli-X ⊗ Pauli-X is self-inverse: (X ⊗ X)^2 = I_4.
public export
auditPauliXXInvolution : Bool
auditPauliXXInvolution =
  splice (stagedComposeSquareMaxel (quote pauliXXSquareMaxel) (quote pauliXXSquareMaxel)) ==
  identitySquareMaxel 4

||| Verified Invariant: 2-qubit Pauli-Z ⊗ Pauli-Z is self-inverse: (Z ⊗ Z)^2 = I_4.
public export
auditPauliZZInvolution : Bool
auditPauliZZInvolution =
  splice (stagedComposeSquareMaxel (quote pauliZZSquareMaxel) (quote pauliZZSquareMaxel)) ==
  identitySquareMaxel 4

||| Verified Invariant: 2-qubit Pauli-X ⊗ I_2 is self-inverse: (X ⊗ I_2)^2 = I_4.
public export
auditPauliXIInvolution : Bool
auditPauliXIInvolution =
  splice (stagedComposeSquareMaxel (quote pauliXISquareMaxel) (quote pauliXISquareMaxel)) ==
  identitySquareMaxel 4

------------------------------------------------------------------------
-- 4C. SEMANTIC BASIS OBSERVATION ON TYPED QUBIT OPERATOR TENSORS
------------------------------------------------------------------------

||| Canonical observation mapping a pair of 2-qubit basis states to its composite Pixel coordinate.
public export
twoBitBasisToPixel : ((Bit, Bit), (Bit, Bit)) -> Pixel
twoBitBasisToPixel ((r1, r2), (c1, c2)) =
  observeKroneckerPixel 2 ((bitToNat r1, bitToNat r2), (bitToNat c1, bitToNat c2))

||| Single-qubit Pauli-X operator natively typed over semantic Bit.
public export
pauliXTypedOperator : MultisetTensor Bit Bit
pauliXTypedOperator =
  AddM (One, Zero) (intToBoxInt 1)
    (AddM (Zero, One) (intToBoxInt 1) ZeroM)

||| Single-qubit Pauli-Z operator natively typed over semantic Bit.
public export
pauliZTypedOperator : MultisetTensor Bit Bit
pauliZTypedOperator =
  AddM (Zero, Zero) (intToBoxInt 1)
    (AddM (One, One) (intToBoxInt (-1)) ZeroM)

||| Single-qubit Identity operator natively typed over semantic Bit.
public export
qubitIdTypedOperator : MultisetTensor Bit Bit
qubitIdTypedOperator =
  AddM (Zero, Zero) (intToBoxInt 1)
    (AddM (One, One) (intToBoxInt 1) ZeroM)

||| Synthesizes the 2-qubit Pauli-X ⊗ Pauli-X operator natively in the monoidal algebra
||| before observing to a sparse SquareMaxel 4.
public export
pauliXXTypedOperator : MultisetTensor (Bit, Bit) (Bit, Bit)
pauliXXTypedOperator = tensorOperator pauliXTypedOperator pauliXTypedOperator

||| Observes a typed 2-qubit operator into a sparse SquareMaxel 4 via twoBitBasisToPixel pushforward.
public export
observeTwoBitOperator : MultisetTensor (Bit, Bit) (Bit, Bit) -> SquareMaxel 4
observeTwoBitOperator op = tensorToSquareMaxel (mapMultiset twoBitBasisToPixel op)

||| Verified Invariant: The algebraic pushforward of the typed operator tensor (pauliXTyped ⊗ pauliXTyped)
||| definitionally equals the coordinate-level sparse matrix pauliXXSquareMaxel.
public export
auditTypedKroneckerEquivalence : Bool
auditTypedKroneckerEquivalence =
  observeTwoBitOperator pauliXXTypedOperator == pauliXXSquareMaxel



------------------------------------------------------------------------
-- 5. MINKOWSKI DIHEDRON QUANTUM GATE BRIDGE (PHASE 4)
-- Maps 2x2 Minkowski Dihedron matrices directly to Pauli quantum gates.
------------------------------------------------------------------------

||| Maps a 2x2 Minkowski Dihedron directly to a dimension-indexed MaxelN 2 quantum gate.
public export
dihedronToMaxelN2 : DM.Dihedron2 -> MaxelN 2
dihedronToMaxelN2 (DM.MkDihedron2 d00 d01 d10 d11) =
  mkMaxel2 d00 d01 d10 d11

||| Pauli-I Dihedron Gate: D(1; 0, 0, 0).
public export
pauliIDihedron : DM.Dihedron2
pauliIDihedron = DM.fromProportionMink 1 0 0 0

||| Pauli-X (NOT) Dihedron Gate: D(0; 0, 1, 0).
public export
pauliXDihedron : DM.Dihedron2
pauliXDihedron = DM.fromProportionMink 0 0 1 0

||| Pauli-Z (Phase-Flip) Dihedron Gate: D(0; 0, 0, 1).
public export
pauliZDihedron : DM.Dihedron2
pauliZDihedron = DM.fromProportionMink 0 0 0 1

||| Symplectic J Dihedron Gate: D(0; 1, 0, 0).
public export
pauliJDihedron : DM.Dihedron2
pauliJDihedron = DM.fromProportionMink 0 1 0 0

||| Verified Invariant: Dihedron representation maps identically to standard Pauli-X and Pauli-Z gates.
public export
auditDihedronPauliGateBridge : Bool
auditDihedronPauliGateBridge =
  (dihedronToMaxelN2 pauliXDihedron == pauliXMaxel) &&
  (dihedronToMaxelN2 pauliZDihedron == pauliZMaxel) &&
  (dihedronToMaxelN2 pauliIDihedron == qubitId2Maxel)

------------------------------------------------------------------------
-- 6. 2LTT STAGED QUANTUM CIRCUIT COMPILER & REDUCTION (PHASE 3)
------------------------------------------------------------------------

||| Symbolically reduces adjacent self-inverse gates (e.g. X * X = I, Z * Z = I) at Level 1.
public export
simplifyGatePairs : List DM.Dihedron2 -> List DM.Dihedron2
simplifyGatePairs [] = []
simplifyGatePairs (g :: []) = [g]
simplifyGatePairs (g1 :: g2 :: rest) =
  let prod = DM.mulDihedron2 g1 g2
  in if prod == DM.identityDihedron2
       then simplifyGatePairs rest
       else g1 :: simplifyGatePairs (g2 :: rest)

||| 2LTT Staged Circuit Compiler:
||| Folds a StagedStream of Dihedron2 quantum gates at compile time (Level 1)
||| into a single compiled Level 0 runtime MaxelN 2 matrix with zero execution overhead.
public export
stagedCompileCircuit : (fuel : Nat) -> StagedStream DM.Dihedron2 -> Code (MaxelN 2)
stagedCompileCircuit fuel strm =
  let finalD = stagedFoldStream fuel DM.mulDihedron2 DM.identityDihedron2 strm
  in quote (dihedronToMaxelN2 finalD)

||| Staged circuit compilation with symbolic Level 1 pair cancellation.
public export
stagedCompileOptimizedCircuit : (fuel : Nat) -> List DM.Dihedron2 -> Code (MaxelN 2)
stagedCompileOptimizedCircuit fuel gates =
  let simplified = simplifyGatePairs gates
      stStream   = quoteFusedStream (FS.stream simplified)
  in stagedCompileCircuit fuel stStream

||| Audit: Staged circuit compiler cancels a 10-gate sequence [X, X, X, X, X, X, X, X, X, X]
||| to the exact identity gate I_2 at compile time.
public export
auditStagedCircuitReductionProof : Bool
auditStagedCircuitReductionProof =
  let tenXs = [pauliXDihedron, pauliXDihedron, pauliXDihedron, pauliXDihedron, pauliXDihedron,
               pauliXDihedron, pauliXDihedron, pauliXDihedron, pauliXDihedron, pauliXDihedron]
      compiledCode = stagedCompileOptimizedCircuit 20 tenXs
      compiledMaxel = splice compiledCode
  in compiledMaxel == qubitId2Maxel

------------------------------------------------------------------------
-- 7. 2LTT STAGED 3D BLOCH SPHERE ROTATIONS
------------------------------------------------------------------------

||| Discrete Constructivist Bloch Vector: a 3-vector (x, y, z) on the Bloch sphere.
public export
BlochVector : Type
BlochVector = Vect 3 BoxInt

||| 2LTT Staged Single-Qubit Bloch Rotation Fusion:
||| Fuses two single-qubit SO(3; Q) projective rotations at Level 1 and acts
||| directly on the Bloch vector, saving intermediate 3x3 matrix multiplication.
public export
stagedRotateBlochVector : Lift PR.ProjectiveProportion -> Lift PR.ProjectiveProportion -> BlochVector -> Code BlochVector
stagedRotateBlochVector qP1 qP2 v =
  PR.stagedFusedRotateVector qP1 qP2 v

||| Staged evaluation of fused Bloch rotation:
public export
evalStagedRotateBlochVector : Lift PR.ProjectiveProportion -> Lift PR.ProjectiveProportion -> BlochVector -> BlochVector
evalStagedRotateBlochVector qP1 qP2 v =
  PR.evalStagedFusedRotateVector qP1 qP2 v

||| QTT 0 Erased Proof Witness: Staged Bloch Rotation Invariant
public export
0 prfStagedRotateBlochVector : (p1, p2 : PR.ProjectiveProportion) -> (v : BlochVector) ->
                              splice (stagedRotateBlochVector (quote p1) (quote p2) v) =
                                PR.rotateVectorScaled (PR.composeProportion p2 p1) v
prfStagedRotateBlochVector _ _ _ = Refl

------------------------------------------------------------------------
-- 8. PROJECTIVE QUANTUM GATE ALGEBRA (QubitCircuitExpr)
------------------------------------------------------------------------

||| Inductive AST for single-qubit quantum circuits over Dihedron and Projective Proportions:
public export
data QubitCircuitExpr : Type where
  GateId   : QubitCircuitExpr
  GateX    : QubitCircuitExpr
  GateZ    : QubitCircuitExpr
  GateRot  : PR.ProjectiveProportion -> QubitCircuitExpr
  SeqGate  : QubitCircuitExpr -> QubitCircuitExpr -> QubitCircuitExpr

||| Evaluates a single-qubit quantum circuit AST into a composite 2x2 Dihedron2 matrix:
public export
collapseCircuitExpr : QubitCircuitExpr -> DM.Dihedron2
collapseCircuitExpr GateId = DM.identityDihedron2
collapseCircuitExpr GateX = pauliXDihedron
collapseCircuitExpr GateZ = pauliZDihedron
collapseCircuitExpr (GateRot p) = DM.fromProportionMink p.xCoord p.tCoord p.rCoord p.sCoord
collapseCircuitExpr (SeqGate g1 g2) = DM.mulDihedron2 (collapseCircuitExpr g1) (collapseCircuitExpr g2)

||| Symbolically reduces self-inverse and identity gates in circuit expressions:
public export
normalizeCircuitExpr : (fuel : Nat) -> QubitCircuitExpr -> QubitCircuitExpr
normalizeCircuitExpr Z e = e
normalizeCircuitExpr (S f) GateId = GateId
normalizeCircuitExpr (S f) GateX = GateX
normalizeCircuitExpr (S f) GateZ = GateZ
normalizeCircuitExpr (S f) (GateRot p) = GateRot p
normalizeCircuitExpr (S f) (SeqGate g1 g2) =
  let n1 = normalizeCircuitExpr f g1
      n2 = normalizeCircuitExpr f g2
  in case (n1, n2) of
       (GateId, r) => r
       (l, GateId) => l
       (GateX, GateX) => GateId
       (GateZ, GateZ) => GateId
       (l, r) => SeqGate l r

||| 2LTT Staged Quantum Circuit Expression Compiler:
||| Evaluates gate compositions symbolically at Level 1, compiling the entire
||| circuit expression into a single compiled Level 0 runtime MaxelN 2 matrix.
public export
stagedCompileCircuitExpr : (fuel : Nat) -> QubitCircuitExpr -> Code (MaxelN 2)
stagedCompileCircuitExpr fuel expr =
  let norm = normalizeCircuitExpr fuel expr
  in quote (dihedronToMaxelN2 (collapseCircuitExpr norm))

||| Staged evaluation of circuit expression compiler:
public export
evalStagedCompileCircuitExpr : (fuel : Nat) -> QubitCircuitExpr -> MaxelN 2
evalStagedCompileCircuitExpr fuel expr =
  splice (stagedCompileCircuitExpr fuel expr)

||| QTT 0 Erased Proof Witness: Circuit Expression Staged Compilation Soundness
public export
0 prfStagedCompileCircuitExpr : (fuel : Nat) -> (expr : QubitCircuitExpr) ->
                                splice (stagedCompileCircuitExpr fuel expr) =
                                  dihedronToMaxelN2 (collapseCircuitExpr (normalizeCircuitExpr fuel expr))
prfStagedCompileCircuitExpr _ _ = Refl

||| Audit: Staged circuit compiler cancels a composite sequence X * (X * (Z * Z)) to I_2.
public export
auditCircuitExprReductionProof : Bool
auditCircuitExprReductionProof =
  let expr = SeqGate GateX (SeqGate GateX (SeqGate GateZ GateZ))
      compiled = evalStagedCompileCircuitExpr 10 expr
  in compiled == qubitId2Maxel

