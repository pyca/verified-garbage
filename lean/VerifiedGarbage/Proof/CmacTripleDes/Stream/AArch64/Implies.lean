module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch

/-!
# Streaming TDEA-CMAC on AArch64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 16 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initAArch64.Implies (streamInitScratchContract AArch64.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initAArch64, AArch64.abi, AArch64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbAArch64.Implies (absorbScratchContract AArch64.abi 0) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbAArch64,
    AArch64.abi, AArch64.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishAArch64.Implies (finishScratchContract AArch64.abi 0) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishAArch64,
    AArch64.abi, AArch64.argRegs] [finishSat] using finishSat

end VG.Proof.CmacTripleDes.Stream.AArch64
