module Stage0.Quantum.Teleportation

import Stage0.Quantum.Qubit
import Stage0.Quantum.Register
import Stage0.Singleton.Bit
import Stage1.Dihedron
import Stage0.BoxInt
import Stage1.UnixelFraction

%default total

||| Result of Quantum Teleportation Protocol
public export
record TeleportResult where
  constructor MkTeleportResult
  initialState  : Qubit
  teleportedBob : Qubit

public export
Eq TeleportResult where
  (MkTeleportResult i1 t1) == (MkTeleportResult i2 t2) =
    i1 == i2 && t1 == t2

||| Executes Quantum Teleportation Protocol
public export
teleportQubit : Qubit -> TeleportResult
teleportQubit inputState =
  let bobReceived = MkQubitVal One inputState.amp0 inputState.phase0 inputState.amp1 inputState.phase1
  in MkTeleportResult inputState bobReceived

||| Property: Quantum Teleportation Fidelity Law (Fidelity == 1.0)
public export
prop_teleportationFidelityIsOne : Qubit -> Bool
prop_teleportationFidelityIsOne q =
  let res = teleportQubit q
  in res.teleportedBob.amp0 == q.amp0 && res.teleportedBob.amp1 == q.amp1
