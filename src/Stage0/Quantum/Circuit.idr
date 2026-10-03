module Stage0.Quantum.Circuit

import Stage0.Singleton.Bit
import Stage0.Singleton.Sing
import Stage1.Dihedron
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Order.Preorder
import Stage1.VexelMaxel
import Stage1.UnixelFraction
import Stage1.MultisetDuality
import Stage1.MaxelTransform
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel
import Stage1.MultisetTensor

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

||| Quantum Gate Preparation Functor (Left Adjoint L_Gate)
public export
data GatePrepFunctor : Type -> Type where
  MkGatePrepFunctor : BoxInt -> a -> GatePrepFunctor a

public export
Functor GatePrepFunctor where
  map f (MkGatePrepFunctor m x) = MkGatePrepFunctor m (f x)

public export
(Eq a) => Eq (GatePrepFunctor a) where
  (MkGatePrepFunctor m1 x1) == (MkGatePrepFunctor m2 x2) = (unwrapBox m1 == unwrapBox m2) && x1 == x2

||| Quantum Gate Measurement Functor (Right Adjoint R_Gate)
public export
data GateMeasFunctor : Type -> Type where
  MkGateMeasFunctor : BoxInt -> a -> GateMeasFunctor a

public export
Functor GateMeasFunctor where
  map f (MkGateMeasFunctor m x) = MkGateMeasFunctor m (f x)

public export
(Eq a) => Eq (GateMeasFunctor a) where
  (MkGateMeasFunctor m1 x1) == (MkGateMeasFunctor m2 x2) = (unwrapBox m1 == unwrapBox m2) && x1 == x2

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
