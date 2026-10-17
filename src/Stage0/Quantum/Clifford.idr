module Stage0.Quantum.Clifford

import Stage0.BoxInt
import Stage1.MultisetTree
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Data.Fuel
import Data.List

%default total

------------------------------------------------------------------------
-- 1. PAULI OPERATORS & CLIFFORD GATES
------------------------------------------------------------------------

||| Single-qubit Pauli operator basis: {I, X, Y, Z}.
public export
data Pauli = PauliI | PauliX | PauliY | PauliZ

public export
Eq Pauli where
  PauliI == PauliI = True
  PauliX == PauliX = True
  PauliY == PauliY = True
  PauliZ == PauliZ = True
  _      == _      = False

public export
Show Pauli where
  show PauliI = "I"
  show PauliX = "X"
  show PauliY = "Y"
  show PauliZ = "Z"

||| Elementary Clifford group generator: Hadamard, Phase (S), and CNOT.
public export
data CliffordGate =
    GateH Nat
  | GateS Nat
  | GateCNOT Nat Nat

public export
Eq CliffordGate where
  (GateH q1)       == (GateH q2)       = q1 == q2
  (GateS q1)       == (GateS q2)       = q1 == q2
  (GateCNOT c1 t1) == (GateCNOT c2 t2) = c1 == c2 && t1 == t2
  _                == _                = False

------------------------------------------------------------------------
-- 2. STABILIZER GENERATORS & TABLEAU REPRESENTATION
------------------------------------------------------------------------

||| A single stabilizer generator: sign bit (True = +1, False = -1) and Pauli string.
public export
record StabilizerGen where
  constructor MkStabGen
  isPositive : Bool
  paulis     : List Pauli

public export
Eq StabilizerGen where
  (MkStabGen s1 p1) == (MkStabGen s2 p2) = s1 == s2 && p1 == p2

public export
Show StabilizerGen where
  show (MkStabGen s ps) =
    (if s then "+" else "-") ++ concatMap show ps

||| Multi-qubit stabilizer state tableau: list of commuting Pauli generators.
public export
record StabilizerTableau where
  constructor MkTableau
  numQubits  : Nat
  generators : List StabilizerGen

public export
Eq StabilizerTableau where
  (MkTableau n1 g1) == (MkTableau n2 g2) = n1 == n2 && g1 == g2

||| Initial |0...0> state tableau for n qubits (generators +Z_1, +Z_2, ..., +Z_n).
public export
initZeroStabilizerTableau : (n : Nat) -> StabilizerTableau
initZeroStabilizerTableau n =
  MkTableau n (map genZ (rangeTo n))
  where
    rangeTo : Nat -> List Nat
    rangeTo Z = []
    rangeTo (S k) = rangeTo k ++ [k]

    makeZRow : Nat -> Nat -> List Pauli
    makeZRow Z _ = []
    makeZRow (S len) targetIdx =
      let p = if len == targetIdx then PauliZ else PauliI
      in p :: makeZRow len targetIdx

    genZ : Nat -> StabilizerGen
    genZ idx = MkStabGen True (makeZRow n idx)

------------------------------------------------------------------------
-- 3. CLIFFORD COMPANION MATRIX STABILIZER STEPPERS
------------------------------------------------------------------------

||| Helper updating an element in a list by index:
public export
updateAt : Nat -> (a -> a) -> List a -> List a
updateAt _ _ [] = []
updateAt Z f (x :: xs) = f x :: xs
updateAt (S k) f (x :: xs) = x :: updateAt k f xs

||| Helper looking up an element in a list by index with fallback:
public export
getAt : Nat -> a -> List a -> a
getAt _ fallback [] = fallback
getAt Z _ (x :: _) = x
getAt (S k) fallback (_ :: xs) = getAt k fallback xs

||| Updates a single Pauli operator under Hadamard gate:
||| H: X -> Z, Z -> X, Y -> -Y, I -> I.
public export
stepPauliH : Pauli -> (Bool, Pauli)
stepPauliH PauliI = (True, PauliI)
stepPauliH PauliX = (True, PauliZ)
stepPauliH PauliZ = (True, PauliX)
stepPauliH PauliY = (False, PauliY)  -- sign flip: H Y H^dagger = -Y

||| Updates a single Pauli operator under Phase (S) gate:
||| S: X -> Y, Y -> -X, Z -> Z, I -> I.
public export
stepPauliS : Pauli -> (Bool, Pauli)
stepPauliS PauliI = (True, PauliI)
stepPauliS PauliX = (True, PauliY)
stepPauliS PauliY = (False, PauliX) -- sign flip: S Y S^dagger = -X
stepPauliS PauliZ = (True, PauliZ)

||| Updates a pair of Paulis (control, target) under CNOT gate:
public export
stepPauliCNOT : Pauli -> Pauli -> (Bool, Pauli, Pauli)
stepPauliCNOT PauliI PauliI = (True, PauliI, PauliI)
stepPauliCNOT PauliI PauliX = (True, PauliI, PauliX)
stepPauliCNOT PauliI PauliY = (True, PauliZ, PauliY)
stepPauliCNOT PauliI PauliZ = (True, PauliZ, PauliZ)
stepPauliCNOT PauliX PauliI = (True, PauliX, PauliX)
stepPauliCNOT PauliX PauliX = (True, PauliX, PauliI)
stepPauliCNOT PauliX PauliY = (True, PauliY, PauliZ)
stepPauliCNOT PauliX PauliZ = (False, PauliY, PauliY)
stepPauliCNOT PauliY PauliI = (True, PauliY, PauliX)
stepPauliCNOT PauliY PauliX = (True, PauliY, PauliI)
stepPauliCNOT PauliY PauliY = (False, PauliX, PauliZ)
stepPauliCNOT PauliY PauliZ = (True, PauliX, PauliY)
stepPauliCNOT PauliZ PauliI = (True, PauliZ, PauliI)
stepPauliCNOT PauliZ PauliX = (True, PauliZ, PauliX)
stepPauliCNOT PauliZ PauliY = (True, PauliI, PauliY)
stepPauliCNOT PauliZ PauliZ = (True, PauliI, PauliZ)

||| Advances a single stabilizer generator under a Clifford gate:
public export
stepGen : CliffordGate -> StabilizerGen -> StabilizerGen
stepGen (GateH q) (MkStabGen s ps) =
  let oldP = getAt q PauliI ps
      (signMod, newP) = stepPauliH oldP
      newSign = if signMod then s else not s
      newPs = updateAt q (const newP) ps
  in MkStabGen newSign newPs
stepGen (GateS q) (MkStabGen s ps) =
  let oldP = getAt q PauliI ps
      (signMod, newP) = stepPauliS oldP
      newSign = if signMod then s else not s
      newPs = updateAt q (const newP) ps
  in MkStabGen newSign newPs
stepGen (GateCNOT c t) (MkStabGen s ps) =
  let pC = getAt c PauliI ps
      pT = getAt t PauliI ps
      (signMod, newPC, newPT) = stepPauliCNOT pC pT
      newSign = if signMod then s else not s
      newPs1 = updateAt c (const newPC) ps
      newPs2 = updateAt t (const newPT) newPs1
  in MkStabGen newSign newPs2

||| Advances the entire stabilizer tableau under a Clifford gate:
public export
stepTableau : CliffordGate -> StabilizerTableau -> StabilizerTableau
stepTableau gate (MkTableau n gens) =
  MkTableau n (map (stepGen gate) gens)

------------------------------------------------------------------------
-- 4. DEFORESTED CLIFFORD CIRCUIT STREAM TRANSDUCERS
------------------------------------------------------------------------

||| Deforested stream generator simulating stabilizer tableau evolution across a Clifford gate stream:
public export
streamCliffordCircuit : List CliffordGate -> StabilizerTableau -> FusedStream StabilizerTableau
streamCliffordCircuit gates initTab =
  unfoldStream nextStep (gates, initTab)
  where
    nextStep : (List CliffordGate, StabilizerTableau) -> Step (List CliffordGate, StabilizerTableau) StabilizerTableau
    nextStep ([], _) = Done
    nextStep (g :: gs, tab) =
      let nextTab = stepTableau g tab
      in Yield nextTab (gs, nextTab)

||| Evaluates a fueled Clifford circuit execution using stream left fold.
public export
fusedRunCliffordCircuit : Fuel -> List CliffordGate -> StabilizerTableau -> StabilizerTableau
fusedRunCliffordCircuit f gates initTab =
  foldStreamFuel f (\_, nextTab => nextTab) initTab (streamCliffordCircuit gates initTab)

||| Evaluates a Nat-step bounded Clifford circuit execution using stream left fold.
public export
fusedRunCliffordCircuitNat : (steps : Nat) -> List CliffordGate -> StabilizerTableau -> StabilizerTableau
fusedRunCliffordCircuitNat steps gates initTab =
  foldStreamNat steps (\acc, nextTab => nextTab) initTab (streamCliffordCircuit gates initTab)

||| Evaluates a model-indexed GohFuel Clifford circuit execution using stream left fold.
public export
fusedRunCliffordCircuitFuelModel : GohFuel cap -> List CliffordGate -> StabilizerTableau -> StabilizerTableau
fusedRunCliffordCircuitFuelModel fuel = fusedRunCliffordCircuitNat (gohSteps fuel)

------------------------------------------------------------------------
-- 5. BALANCED MULTISET-TREE QUANTUM AMPLITUDE CARRIER (O(log N))
------------------------------------------------------------------------

||| Sparse quantum state vector backed by balanced AVL MultisetTrees for positive and negative amplitudes:
||| Replaces linear association lists with O(log N) lookup and insertion (Rule 04).
public export
record TreeStateVector where
  constructor MkTreeState
  posTree : MultisetTree Nat
  negTree : MultisetTree Nat

public export
emptyTreeState : TreeStateVector
emptyTreeState = MkTreeState Leaf Leaf

||| Lookups amplitude of computational basis state |idx> in O(log N) time:
public export
lookupTreeAmplitude : Nat -> TreeStateVector -> BoxInt
lookupTreeAmplitude idx (MkTreeState p n) =
  let posCount = lookupTokenTree idx p
      negCount = lookupTokenTree idx n
      posBox = natToBoxInt posCount
      negBoxVal = natToBoxInt negCount
  in subBox posBox negBoxVal

||| Inserts/adds amplitude to computational basis state |idx> with AVL rebalancing:
public export
insertTreeAmplitude : Nat -> BoxInt -> TreeStateVector -> TreeStateVector
insertTreeAmplitude idx amp (MkTreeState p n) =
  let w = unwrapBox amp
  in if w > 0
       then MkTreeState (insertTokenTree idx (integerToNat w) p) n
       else if w < 0
         then MkTreeState p (insertTokenTree idx (integerToNat (-w)) n)
         else MkTreeState p n

||| Total quantum state norm / token sum from balanced trees:
public export
treeStateNorm : TreeStateVector -> Nat
treeStateNorm (MkTreeState p n) =
  treeTokenSum p + treeTokenSum n

------------------------------------------------------------------------
-- 6. INVARIANT AUDITS
------------------------------------------------------------------------

||| Audits Clifford Bell State Preparation:
||| Starting from 2-qubit |00> with stabilizers {+Z_0 I_1, +I_0 Z_1}:
||| 1. Apply GateH 0 -> stabilizers {+X_0 I_1, +I_0 Z_1}.
||| 2. Apply GateCNOT 0 1 -> stabilizers {+X_0 X_1, +Z_0 Z_1} (exact Bell state |Phi+>).
public export
auditCliffordBellStabilizerProof : Bool
auditCliffordBellStabilizerProof =
  let initTab = MkTableau 2 [ MkStabGen True [PauliZ, PauliI]
                            , MkStabGen True [PauliI, PauliZ] ]
      bellTab = fusedRunCliffordCircuitFuelModel ellipticGohFuelModel [GateH 0, GateCNOT 0 1] initTab
      expected = MkTableau 2 [ MkStabGen True [PauliX, PauliX]
                             , MkStabGen True [PauliZ, PauliZ] ]
  in bellTab == expected

||| Audits MultisetTree logarithmic amplitude operations:
||| 1. Insert amplitudes for |0>, |1>, |2>.
||| 2. Verify tree amplitude lookup matches exactly.
||| 3. Total tree norm is conserved.
public export
auditMultisetTreeAmplitudesProof : Bool
auditMultisetTreeAmplitudesProof =
  let s0 = emptyTreeState
      s1 = insertTreeAmplitude 0 (intToBoxInt 3) s0
      s2 = insertTreeAmplitude 1 (intToBoxInt (-4)) s1
      s3 = insertTreeAmplitude 2 (intToBoxInt 5) s2
      a0 = lookupTreeAmplitude 0 s3
      a1 = lookupTreeAmplitude 1 s3
      a2 = lookupTreeAmplitude 2 s3
      normVal = treeStateNorm s3
  in unwrapBox a0 == 3 && unwrapBox a1 == (-4) && unwrapBox a2 == 5 && normVal == 12

||| Combined audit verifying Clifford stabilizer steppers and MultisetTree amplitudes.
public export
auditCliffordTotalityProof : Bool
auditCliffordTotalityProof =
  auditCliffordBellStabilizerProof &&
  auditMultisetTreeAmplitudesProof
