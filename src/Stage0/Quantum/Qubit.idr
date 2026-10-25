module Stage0.Quantum.Qubit

import Stage0.Singleton.Bit
import Stage0.Singleton.Sing
import Stage1.Dihedron
import public Stage0.BoxInt
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction

%default total

||| A Qubit State |ψ⟩ = α|0⟩ + β|1⟩ over payload basis value pVal.
public export
record QubitVal pVal where
  constructor MkQubitVal
  wireVal : pVal
  amp0    : BoxInt   -- Amplitude for |0⟩
  phase0  : Dihedron -- Phase vector for |0⟩
  amp1    : BoxInt   -- Amplitude for |1⟩
  phase1  : Dihedron -- Phase vector for |1⟩

public export
Qubit : Type
Qubit = QubitVal Bit

public export
(Eq pVal) => Eq (QubitVal pVal) where
  (MkQubitVal w1 a0 ph0 a1 ph1) == (MkQubitVal w2 b0 qh0 b1 qh1) =
    w1 == w2 && a0.value == b0.value && ph0 == qh0 && a1.value == b1.value && ph1 == qh1

public export
(Show pVal) => Show (QubitVal pVal) where
  show (MkQubitVal w a0 p0 a1 p1) =
    "[Qubit wire=" ++ show w ++ " | |0>: amp=" ++ show a0 ++ " phase=(" ++ show p0 ++ ")" ++
    " | |1>: amp=" ++ show a1 ++ " phase=(" ++ show p1 ++ ")]"

-----------------------------------------------------------------------
-- FUNCTOR, APPLICATIVE & MONAD IMPLEMENTATIONS
-----------------------------------------------------------------------

public export
Functor QubitVal where
  map f (MkQubitVal w a0 p0 a1 p1) = MkQubitVal (f w) a0 p0 a1 p1

public export
Applicative QubitVal where
  pure x = MkQubitVal x 1 (MkDihedron 1 0 0 0) 0 (MkDihedron 0 0 0 0)
  (MkQubitVal f a0 p0 a1 p1) <*> (MkQubitVal x b0 q0 b1 q1) =
    MkQubitVal (f x) (a0 * b0) (mulDihedron p0 q0) (a1 * b1) (mulDihedron p1 q1)

public export
Monad QubitVal where
  (MkQubitVal x a0 p0 a1 p1) >>= f =
    let MkQubitVal y b0 q0 b1 q1 = f x
    in MkQubitVal y (a0 * b0) (mulDihedron p0 q0) (a1 * b1) (mulDihedron p1 q1)

-----------------------------------------------------------------------
-- QUBIT CONSTRUCTORS
-----------------------------------------------------------------------

||| Pure Basis State |0⟩
public export
qubitZero : Bit -> Qubit
qubitZero b = MkQubitVal b 1 (MkDihedron 1 0 0 0) 0 (MkDihedron 0 0 0 0)

||| Pure Basis State |1⟩
public export
qubitOne : Bit -> Qubit
qubitOne b = MkQubitVal b 0 (MkDihedron 0 0 0 0) 1 (MkDihedron 1 0 0 0)

-----------------------------------------------------------------------
-- QUANTUM GATES
-----------------------------------------------------------------------

||| Pauli-X Gate (Quantum NOT Gate): Swaps |0⟩ ↔ |1⟩ via negBit
public export
gateX : Qubit -> Qubit
gateX (MkQubitVal w a0 p0 a1 p1) = MkQubitVal (negBit w) a1 p1 a0 p0

||| Pauli-Z Gate (Phase Flip Gate): Flips the phase of |1⟩ by π (negDihedron)
public export
gateZ : Qubit -> Qubit
gateZ (MkQubitVal w a0 p0 a1 p1) = MkQubitVal w a0 p0 a1 (negDihedron p1)

||| Hadamard Gate (H): Puts pure basis state into equal superposition
public export
gateH : Qubit -> Qubit
gateH (MkQubitVal w a0 p0 a1 p1) =
  let inPhase = MkDihedron 1 0 0 0
  in MkQubitVal w 1 inPhase 1 inPhase

-----------------------------------------------------------------------
-- MEASUREMENT PROBABILITIES
-----------------------------------------------------------------------

||| Exact Rational Probability P(|0⟩) = |amp0|² / (|amp0|² + |amp1|²)
public export
probZero : QubitVal pVal -> UnixelFraction
probZero (MkQubitVal _ a0 _ a1 _) =
  let i0 = a0 * a0
      i1 = a1 * a1
      iTotal = i0 + i1
      denNat = if iTotal.value > 0 then Prelude.integerToNat iTotal.value else 1
  in mkUnixelFraction i0 denNat

||| Exact Rational Probability P(|1⟩) = |amp1|² / (|amp0|² + |amp1|²)
public export
probOne : QubitVal pVal -> UnixelFraction
probOne (MkQubitVal _ a0 _ a1 _) =
  let i0 = a0 * a0
      i1 = a1 * a1
      iTotal = i0 + i1
      denNat = if iTotal.value > 0 then Prelude.integerToNat iTotal.value else 1
  in mkUnixelFraction i1 denNat

-----------------------------------------------------------------------
-- VERIFIED QUBIT PROPERTIES
-----------------------------------------------------------------------

||| Property 1: Pauli-X Involution Law (X(X |ψ⟩) == |ψ⟩)
public export
prop_pauliXInvolution : Qubit -> Bool
prop_pauliXInvolution q = gateX (gateX q) == q

||| Property 2: Qubit Probability Normalization Law (P(|0⟩) + P(|1⟩) == 1.0)
public export
prop_probabilityNormalized : Qubit -> Bool
prop_probabilityNormalized q =
  let p0 = probZero q
      p1 = probOne q
      tot = addUnixelFraction p0 p1
  in tot.num == natToBoxInt (unwrapUnixel tot.den)
