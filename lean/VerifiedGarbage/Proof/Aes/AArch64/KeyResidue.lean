module

public import VerifiedGarbage.Impl.Aes.AArch64.Fn
public meta import VerifiedGarbage.Impl.Aes.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public meta import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.Frame
public meta import VerifiedGarbage.Proof.Aes.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES's key expansion on AArch64 returns without secret residue

`vg_aes_expand_key` and `vg_aes_expand_key_aes` run in a frame of 512 bytes
whose scratch words they zero (`withStackScratchWiped 512 .x3 64`). The
analysis of the window's bytes (`rtaintG`) finds every byte of it the same in
both runs on return, so they need no clearing of the stack
(`noResidue_of_doneG`), only of what they leave in their registers.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.KeyResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_aes_expand_key`. -/
abbrev expandKeyCode : Prog isa := Impl.Aes.AArch64.Fn.expandKey

theorem expandKeyCode_verified : Verified AArch64.target expandKeyCode (Spec.Aes.expandKeyContract AArch64.abi 512) :=
  Clears.Verified.withClears (Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.expandKey_verified) (by decide)

theorem expandKeyCode_noResidue : NoResidue expandKeyCode (Spec.Aes.expandKeyContract AArch64.abi 512) 0 :=
  noResidue_of_doneG expandKeyCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Aes.expandKeyApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_aes_expand_key_aes`. -/
abbrev expandKeyAesCode : Prog isa := Impl.Aes.AArch64.Fn.expandKeyAes

theorem expandKeyAesCode_verified : Verified AArch64.target expandKeyAesCode (Spec.Aes.expandKeyContract AArch64.abi 512) :=
  Clears.Verified.withClears (Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.Aese.Key.expandKey_verified) (by decide)

theorem expandKeyAesCode_noResidue : NoResidue expandKeyAesCode (Spec.Aes.expandKeyContract AArch64.abi 512) 0 :=
  noResidue_of_doneG expandKeyAesCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Aes.expandKeyApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Aes.AArch64.KeyResidue.expandKeyCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Aes.AArch64.Fn.expandKey
      (Spec.Aes.expandKeyContract AArch64.abi 512) 0 :=
  ⟨Proof.Aes.AArch64.KeyResidue.expandKeyCode_verified,
    Proof.Aes.AArch64.KeyResidue.expandKeyCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Aes.AArch64.Fn.expandKeyAes
      (Spec.Aes.expandKeyContract AArch64.abi 512) 0 :=
  ⟨Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_verified,
    Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_noResidue⟩

end VG.Proof.Aes.AArch64.KeyResidue
