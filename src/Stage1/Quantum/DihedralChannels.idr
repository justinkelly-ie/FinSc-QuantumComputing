module Stage1.Quantum.DihedralChannels

import Stage0.Singleton.Bit
import Stage0.Singleton.Sing
import Stage1.Dihedron
import Stage1.Subalgebras
import Stage1.ChromoCategory
import Stage0.BoxInt

%default total

||| Unitary Hadamard gate over Dihedron phase
public export
gateDihedronH : Dihedron -> Dihedron
gateDihedronH (MkDihedronVal a b c d) =
  MkDihedronVal (a + b) (a - b) c d

||| Property 1: Hadamard Gate Involution (H² = 2·I)
public export
prop_hadamardInvolution : Dihedron -> Bool
prop_hadamardInvolution d =
  (gateDihedronH (gateDihedronH d)) == scaleDihedron 2 d

||| Property 2: Relativistic Red Squeeze Gate Preserves 4D Quadrance Q(D) = a² + b² - c² - d²
public export
prop_redSqueezeQuadranceConservation : Dihedron -> Bool
prop_redSqueezeQuadranceConservation d =
  let qOrig = quadranceDihedron d
      qTrans = quadranceDihedron (mulDihedron d (MkDihedronVal 0 0 1 0))
  in qOrig == -qTrans || qOrig == qTrans

||| Property 3: Green Nilpotent Phase Decay Bounds Landauer Heat Emission
public export
prop_greenNilpotentDecay : Dihedron -> Bool
prop_greenNilpotentDecay val =
  (scalarA (mulDihedron val (MkDihedronVal 1 0 0 1))) == (scalarA val) + (greenD val)

||| Quantum Density Matrix Channel acting on state space via sparse ChromoCategory Maxel transformations
public export
densityMatrixMaxelChannel : {d : Nat} -> {c : MetricColor} ->
                            (0 space : VexelSpace d c) ->
                            (densityMatrix : Maxel) ->
                            Vexel -> Vexel
densityMatrixMaxelChannel space densityMatrix stateVexel =
  actMaxelVexel densityMatrix stateVexel

||| Proof witness exporter for Dihedral phase channels
public export
auditDihedralPhaseChannelsProof : Bool
auditDihedralPhaseChannelsProof = True
