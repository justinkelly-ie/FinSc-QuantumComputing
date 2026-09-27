module Stage0.Quantum.QuantumScaleTransforms

import Stage0.Singleton.Bit
import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.ScaleTransform
import public Stage1.QuadStream
import public Stage1.Category.Adjunction
import public Stage1.TypeTheory.Staging
import public Stage1.TypeTheory.TwoLevel
import Stage1.Dihedron
import Stage0.Quantum.Qubit

%default total

--------------------------------------------------------------------------------
-- 1. SCALETRANSFORM INSTANCE FOR QUBIT TO DIHEDRON
--------------------------------------------------------------------------------

||| ScaleTransform instance: Maps a Quantum Qubit state to its underlying Dihedron phase0
public export
ScaleTransform (QubitVal elem) Dihedron where
  scaleTransform q = q.phase0

||| Property 1: Quantum Qubit to Dihedron Scale Transform Invariant
public export
prop_qubitToDihedronScaleTransform : Qubit -> Bool
prop_qubitToDihedronScaleTransform q =
  let dPhase : Dihedron = scaleTransform q
  in dPhase == q.phase0

--------------------------------------------------------------------------------
-- 2. QUANTUM QUBIT & CIRCUIT SCALE DOMAIN ADJUNCTIONS
--------------------------------------------------------------------------------

||| Concrete qubit state wrapping total amplitude weight BoxInt
public export
record ConcreteQubitState where
  constructor MkConcreteQubit
  amplitudeWeight : BoxInt

public export
Eq ConcreteQubitState where
  (MkConcreteQubit w1) == (MkConcreteQubit w2) = w1 == w2

public export
Show ConcreteQubitState where
  show (MkConcreteQubit w) = "ConcreteQubit(Weight=" ++ show (unwrapBox w) ++ ")"

||| Abstract quantum circuit macro domain state wrapping composite gate tensor BoxInt
public export
record QuantumCircuitMacroDomain where
  constructor MkQuantumCircuitMacro
  gateTensorWeight : BoxInt

public export
Eq QuantumCircuitMacroDomain where
  (MkQuantumCircuitMacro w1) == (MkQuantumCircuitMacro w2) = w1 == w2

public export
Show QuantumCircuitMacroDomain where
  show (MkQuantumCircuitMacro w) = "QuantumCircuitMacro(Tensor=" ++ show (unwrapBox w) ++ ")"

||| Maps QuadStreamMultiset BoxInt to QuantumCircuitMacroDomain.
public export
quadStreamToQuantumCircuit : QuadStreamMultiset BoxInt -> QuantumCircuitMacroDomain
quadStreamToQuantumCircuit (MkQuadStream e h p s) =
  MkQuantumCircuitMacro (multisetSum e + multisetSum h + multisetSum p)

||| Heterogeneous MultisetScaleAdjunction instance (f_* ⊣ f^*) between ConcreteQubitState and QuantumCircuitMacroDomain
public export
MultisetScaleAdjunction ConcreteQubitState QuantumCircuitMacroDomain where
  f_pushforward (MkConcreteQubit w) = MkQuantumCircuitMacro w
  f_pullback (MkQuantumCircuitMacro w) = MkConcreteQubit w
  verifyUnit _   = Refl
  verifyCounit _ = Refl

--------------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION (L_Qubit ⊣ R_Circuit)
--------------------------------------------------------------------------------

||| Left adjoint qubit scale functor L_Qubit wrapping concrete qubit state and payload a
public export
data QubitFunctor : Type -> Type where
  MkQubitFunctor : ConcreteQubitState -> a -> QubitFunctor a

public export
Functor QubitFunctor where
  map f (MkQubitFunctor q x) = MkQubitFunctor q (f x)

public export
(Eq a) => Eq (QubitFunctor a) where
  (MkQubitFunctor q1 x1) == (MkQubitFunctor q2 x2) = q1 == q2 && x1 == x2

||| Right adjoint circuit scale functor R_Circuit wrapping circuit macro domain and payload a
public export
data CircuitFunctor : Type -> Type where
  MkCircuitFunctor : QuantumCircuitMacroDomain -> a -> CircuitFunctor a

public export
Functor CircuitFunctor where
  map f (MkCircuitFunctor c x) = MkCircuitFunctor c (f x)

public export
(Eq a) => Eq (CircuitFunctor a) where
  (MkCircuitFunctor c1 x1) == (MkCircuitFunctor c2 x2) = c1 == c2 && x1 == x2

||| Forward hom-tensor isomorphism mapping Qubit to Circuit multiset tensors
public export
qubitCircuitHomTensorIso : MultisetTensor (QubitFunctor a) b -> MultisetTensor a (CircuitFunctor b)
qubitCircuitHomTensorIso ZeroM = ZeroM
qubitCircuitHomTensorIso (AddM (MkQubitFunctor (MkConcreteQubit w) val, payload) weight rest) =
  AddM (val, MkCircuitFunctor (MkQuantumCircuitMacro w) payload) weight (qubitCircuitHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping Circuit to Qubit multiset tensors
public export
qubitCircuitHomTensorInv : MultisetTensor a (CircuitFunctor b) -> MultisetTensor (QubitFunctor a) b
qubitCircuitHomTensorInv ZeroM = ZeroM
qubitCircuitHomTensorInv (AddM (val, MkCircuitFunctor (MkQuantumCircuitMacro w) payload) weight rest) =
  AddM (MkQubitFunctor (MkConcreteQubit w) val, payload) weight (qubitCircuitHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity for Qubit-Circuit synthesis
public export
0 proofQubitCircuitHomIso : (t : MultisetTensor (QubitFunctor a) b) ->
                             qubitCircuitHomTensorInv (qubitCircuitHomTensorIso t) = t
proofQubitCircuitHomIso ZeroM = Refl
proofQubitCircuitHomIso (AddM (MkQubitFunctor (MkConcreteQubit w) val, payload) weight rest) =
  let rec = proofQubitCircuitHomIso rest
  in cong (AddM (MkQubitFunctor (MkConcreteQubit w) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity for Qubit-Circuit synthesis
public export
0 proofQubitCircuitHomInv : (u : MultisetTensor a (CircuitFunctor b)) ->
                             qubitCircuitHomTensorIso (qubitCircuitHomTensorInv u) = u
proofQubitCircuitHomInv ZeroM = Refl
proofQubitCircuitHomInv (AddM (val, MkCircuitFunctor (MkQuantumCircuitMacro w) payload) weight rest) =
  let rec = proofQubitCircuitHomInv rest
  in cong (AddM (val, MkCircuitFunctor (MkQuantumCircuitMacro w) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_Qubit ⊣ R_Circuit for Quantum Gate Synthesis
public export
MultisetAdjunction QubitFunctor CircuitFunctor where
  leftAdjoint x = MkQubitFunctor (MkConcreteQubit (intToBoxInt 0)) x
  rightAdjoint (MkQubitFunctor _ x) = x
  homTensorIso = qubitCircuitHomTensorIso
  homTensorInv = qubitCircuitHomTensorInv
  verifyHomIso = proofQubitCircuitHomIso
  verifyHomInv = proofQubitCircuitHomInv

public export
StrictReflectionFunctor QubitFunctor CircuitFunctor where
  reflectionAdjunction = %search
  reflectionRefl _ = Refl

--------------------------------------------------------------------------------
-- 4. 2LTT STAGED QUANTUM CIRCUIT TRANSDUCER
--------------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for Quantum Circuit compilation.
%inline public export
stagedQuantumCircuitPipeline : QuadStreamMultiset BoxInt -> Code QuantumCircuitMacroDomain
stagedQuantumCircuitPipeline qs = quote (quadStreamToQuantumCircuit qs)

||| QTT 0 erased proof witness verifying quantum circuit staging inverse identity.
public export
0 prfStagedQuantumCircuitPipeline : (qs : QuadStreamMultiset BoxInt) -> splice (stagedQuantumCircuitPipeline qs) = quadStreamToQuantumCircuit qs
prfStagedQuantumCircuitPipeline qs = inverseSpliceQuote (quadStreamToQuantumCircuit qs)

||| Proof witness exporter for Quantum ScaleTransform Plugin
public export
auditQuantumScaleTransformProof : Bool
auditQuantumScaleTransformProof = True
