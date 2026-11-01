module

public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.Scratch
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Cmac.TripleDesContract

/-!
# TDEA-CMAC on x86-64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), under which the streaming functions
run this code inline (`Proof/CmacTripleDes/Stream/X86_64/Inline.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86_64.Implies (initScratchContract X86_64.abi 0) := by
  sig_implies [initScratchContract, initScratchSig, Proof.Cmac.tdesInitPre, Proof.Cmac.tdesInitPost,
    initX86_64, X86_64.abi,
    X86_64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem update_implies : updateX86_64.Implies (updateScratchContract X86_64.abi 0) := by
  sig_implies [updateScratchContract, updateScratchSig, Proof.Cmac.tdesUpdatePost, updateX86_64,
    X86_64.abi,
    X86_64.argRegs] [updSat] using updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeX86_64.Implies (finalizeScratchContract X86_64.abi 0) := by
  sig_implies [finalizeScratchContract, finalizeScratchSig, Proof.Cmac.tdesFinalizePre,
    Proof.Cmac.tdesFinalizePost, finalizeX86_64, X86_64.abi,
    X86_64.argRegs] [finSat] using finSat

end VG.Proof.CmacTripleDes.X86_64
