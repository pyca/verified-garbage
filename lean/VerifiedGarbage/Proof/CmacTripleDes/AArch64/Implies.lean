import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacTripleDes.Scratch

/-!
# TDEA-CMAC on AArch64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initAArch64.Implies (initScratchContract AArch64.abi 0) := by
  sig_implies [initScratchContract, initScratchSig, Spec.Cmac.tdesInitPre, Spec.Cmac.tdesInitPost,
    initAArch64, AArch64.abi,
    AArch64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem update_implies : updateAArch64.Implies (updateScratchContract AArch64.abi 0) := by
  sig_implies [updateScratchContract, updateScratchSig, Spec.Cmac.tdesUpdatePost, updateAArch64,
    AArch64.abi,
    AArch64.argRegs] [updSat] using updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeAArch64.Implies (finalizeScratchContract AArch64.abi 0) := by
  sig_implies [finalizeScratchContract, finalizeScratchSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, finalizeAArch64, AArch64.abi,
    AArch64.argRegs] [finSat] using finSat

end VG.Proof.CmacTripleDes.AArch64
