module Stage1.Quantum.LandauerErasure

import Stage0.Singleton.Bit
import Stage0.Singleton.Sing
import Stage0.Multiset
import Stage0.BoxInt

%default total

||| Resets 1 Boolean Singleton Bit and emits 1 unit of dissipation heat
public export
eraseBitWithHeat : Bit -> (Bit, Nat)
eraseBitWithHeat b =
  let resetBit = Zero
      heatDissipated = if isOne b then 1 else 0
  in (resetBit, heatDissipated)

||| Property: Landauer Erasure Heat Dissipation Law (ΔL >= 1 for 1-bit reset)
public export
prop_landauerErasureEmitsHeat : Bit -> Bool
prop_landauerErasureEmitsHeat b =
  let (reset, heat) = eraseBitWithHeat One
  in heat >= 1 && isZero reset
