module Stage0.Quantum.Register

import Stage0.Quantum.Qubit
import Stage1.Dihedron
import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.UnixelFraction
import Data.Vect

%default total

||| A 2-Qubit Entangled State (|00⟩, |01⟩, |10⟩, |11⟩)
public export
record QubitRegister2 where
  constructor MkRegister2
  amp00 : Stage0.BoxInt.BoxInt
  amp01 : Stage0.BoxInt.BoxInt
  amp10 : Stage0.BoxInt.BoxInt
  amp11 : Stage0.BoxInt.BoxInt

public export
Eq QubitRegister2 where
  (MkRegister2 a00 a01 a10 a11) == (MkRegister2 b00 b01 b10 b11) =
    a00 == b00 && a01 == b01 && a10 == b10 && a11 == b11

public export
Show QubitRegister2 where
  show (MkRegister2 a00 a01 a10 a11) =
    "[2-Qubit Reg | |00>: " ++ show a00 ++ " | |01>: " ++ show a01 ++
    " | |10>: " ++ show a10 ++ " | |11>: " ++ show a11 ++ "]"

-----------------------------------------------------------------------
-- BELL STATE CREATION & CNOT GATES
-----------------------------------------------------------------------

||| Creates an Un-entangled |00⟩ State
public export
regZeroZero : QubitRegister2
regZeroZero = MkRegister2 1 0 0 0

||| 2-Qubit Controlled-NOT (CNOT) Gate
||| Flips target qubit if control qubit is |1⟩.
public export
gateCNOT : QubitRegister2 -> QubitRegister2
gateCNOT (MkRegister2 a00 a01 a10 a11) =
  MkRegister2 a00 a01 a11 a10

||| Creates Maximally Entangled Bell State |Φ⁺⟩ = (|00⟩ + |11⟩) / √2
||| Method: Apply Hadamard to Qubit 0, then CNOT(0, 1)
public export
bellStatePhiPlus : QubitRegister2
bellStatePhiPlus =
  let hState = MkRegister2 1 0 1 0
  in gateCNOT hState

-----------------------------------------------------------------------
-- MEASUREMENT PROBABILITIES FOR 2-QUBIT REGISTER
-----------------------------------------------------------------------

||| Computes exact probability P(|00⟩)
public export
prob00 : QubitRegister2 -> UnixelFraction
prob00 (MkRegister2 a00 a01 a10 a11) =
  let i00 = a00 * a00
      i01 = a01 * a01
      i10 = a10 * a10
      i11 = a11 * a11
      tot = i00 + i01 + i10 + i11
      denNat = if tot.value > 0 then Prelude.integerToNat tot.value else 1
  in mkUnixelFraction i00 denNat

||| Computes exact probability P(|11⟩)
public export
prob11 : QubitRegister2 -> UnixelFraction
prob11 (MkRegister2 a00 a01 a10 a11) =
  let i00 = a00 * a00
      i01 = a01 * a01
      i10 = a10 * a10
      i11 = a11 * a11
      tot = i00 + i01 + i10 + i11
      denNat = if tot.value > 0 then Prelude.integerToNat tot.value else 1
  in mkUnixelFraction i11 denNat

-----------------------------------------------------------------------
-- VERIFIED ENTANGLEMENT PROPERTIES
-----------------------------------------------------------------------

||| Property: Bell State |Φ⁺⟩ Max Entanglement Law
||| For Bell State |Φ⁺⟩: P(|00⟩) = 1/2, P(|11⟩) = 1/2, P(|01⟩) = 0, P(|10⟩) = 0.
public export
prop_bellStateIsEntangled : Bool
prop_bellStateIsEntangled =
  let bell = bellStatePhiPlus
      p00 = prob00 bell
      p11 = prob11 bell
  in p00.num == 1 && unwrapUnixel p00.den == 2 &&
     p11.num == 1 && unwrapUnixel p11.den == 2 &&
     bell.amp01 == 0 && bell.amp10 == 0

-----------------------------------------------------------------------
-- COMONADIC QUANTUM WAVE CONTEXT & ENTANGLEMENT DENSITY
-----------------------------------------------------------------------

||| Comonadic Quantum Wave Context wrapping a focus payload and multi-qubit register.
public export
record QuantumWaveContext (a : Type) where
  constructor MkQuantumWaveContext
  focus : a
  register : QubitRegister2

public export
Functor QuantumWaveContext where
  map f (MkQuantumWaveContext x reg) = MkQuantumWaveContext (f x) reg

||| Standard Comonad interface for QuantumWaveContext enabling extract, duplicate.
public export
interface Functor w => Comonad (0 w : Type -> Type) where
  extract : w a -> a
  duplicate : w a -> w (w a)

||| Standard Comonad instance for QuantumWaveContext enabling extract, duplicate.
public export
Comonad QuantumWaveContext where
  extract (MkQuantumWaveContext x _) = x
  duplicate ctx@(MkQuantumWaveContext _ reg) = MkQuantumWaveContext ctx reg

||| Evaluates zero-allocation quantum entanglement density over a QuantumWaveContext.
public export
coevalEntanglementDensity : QuantumWaveContext a -> BoxInt
coevalEntanglementDensity (MkQuantumWaveContext _ (MkRegister2 a00 a01 a10 a11)) =
  -- Determinant |a00*a11 - a01*a10| measures 2-qubit concurrence entanglement
  absBox ((a00 * a11) - (a01 * a10))

||| Audit proof verifying maximal concurrence entanglement density on Bell State |Φ⁺⟩.
public export
auditQuantumComonadProof : Bool
auditQuantumComonadProof =
  let bellCtx = MkQuantumWaveContext "BellPhiPlus" bellStatePhiPlus
      entDensity = coevalEntanglementDensity bellCtx
  in entDensity == intToBoxInt 1
