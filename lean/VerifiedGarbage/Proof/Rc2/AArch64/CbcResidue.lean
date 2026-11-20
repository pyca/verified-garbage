module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Chained
public meta import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Chained
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public meta import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.AArch64.Key
public meta import VerifiedGarbage.Proof.Rc2.AArch64.Key
public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
public meta import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# RC2-CBC on AArch64 returns without secret residue

`vg_rc2_cbc_encrypt_chained` and `vg_rc2_cbc_decrypt_chained` run in a
512-byte frame whose scratch words they zero (`withStackScratchWiped`). The
analysis of the window's bytes (`rtaintG`) finds every byte of it the same in
both runs on return, so they need no clearing of the stack
(`noResidue_of_doneG`), only of what they leave in their registers.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.CbcResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-- `vg_rc2_cbc_encrypt_chained`. -/
abbrev cbcEncryptChainedCode : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x7, .x8]
    [.v0, .v1, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.encrypt)

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Rc2.cbcEncryptChainedContract AArch64.abi 512) :=
  Clears.Verified.withClears (Proof.Rc2.AArch64.Cbc.encryptChained_framed) (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Rc2.cbcEncryptChainedContract AArch64.abi 512) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Rc2.cbcEncryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_rc2_cbc_decrypt_chained`. -/
abbrev cbcDecryptChainedCode : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.decrypt)

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Rc2.cbcDecryptChainedContract AArch64.abi 512) :=
  Clears.Verified.withClears (Proof.Rc2.AArch64.Cbc.decryptChained_framed) (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Rc2.cbcDecryptChainedContract AArch64.abi 512) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Rc2.cbcDecryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode
      (Spec.Rc2.cbcEncryptChainedContract AArch64.abi 512) 0 :=
  ⟨Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_verified,
    Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode
      (Spec.Rc2.cbcDecryptChainedContract AArch64.abi 512) 0 :=
  ⟨Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_verified,
    Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_noResidue⟩

end VG.Proof.Rc2.AArch64.CbcResidue
