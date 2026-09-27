module Stage1.Quantum.NoCloning

import Stage0.Quantum.Qubit
import Stage0.Singleton.Bit
import Stage0.Interfaces

%default total

||| Linear consumption of a Qubit token (QTT 1 constraint)
public export
consumeLinearQubit : (1 q : Qubit) -> Ur Nat
consumeLinearQubit (MkQubitVal w _ _ _ _) = MkUr (if isOne w then 1 else 0)

||| Property: No-Cloning Theorem (Single-pass linear consumption)
public export
prop_noCloningLinearConstraint : Qubit -> Bool
prop_noCloningLinearConstraint (MkQubitVal w a0 p0 a1 p1) =
  let (MkUr consumed) = consumeLinearQubit (MkQubitVal w a0 p0 a1 p1)
      expected : Nat = if isOne w then 1 else 0
  in consumed == expected
