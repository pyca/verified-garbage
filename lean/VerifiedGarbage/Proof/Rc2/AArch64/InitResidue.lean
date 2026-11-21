module

public import VerifiedGarbage.Impl.Rc2.AArch64.Fn
public meta import VerifiedGarbage.Impl.Rc2.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
public meta import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
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
# RC2-CBC's initialization on AArch64 returns without secret residue

`vg_rc2_cbc_init` runs in a frame whose scratch words it zeroes, and calls the
key expansion, whose frame lies below it. The analysis of the window's bytes
(`rtaintG`) finds that only the lowest 16-byte granule of its 592-byte window
may differ between the two runs on return. It clears its registers, then
zeroes that granule (`scrubSel 592 [0]`); its postcondition reads the
memory on return only within its buffers (`Proof.Rc2.cbcInitPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.InitResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_rc2_cbc_init`, before its granules [0] are zeroed. -/
abbrev cbcInitBase : Prog isa := Impl.Rc2.AArch64.Fn.cbcInitBase

theorem cbcInitBase_verified : Verified AArch64.target cbcInitBase (Spec.Rc2.cbcInitContract AArch64.abi 592) :=
  Clears.Verified.withClears (Proof.Rc2.AArch64.Stream.init_framed) (by decide)

theorem cbcInitScrubOk : RTaintF.ScrubOk (Spec.Rc2.cbcInitContract AArch64.abi 592) 592 :=
  RTaintF.scrubOk_regs (sig := Spec.Rc2.cbcInitApi.sig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Rc2.cbcInitPostOut_local _)

/-- `vg_rc2_cbc_init`. -/
abbrev cbcInitCode : Prog isa := Impl.Rc2.AArch64.Fn.cbcInit

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Rc2.AArch64.InitResidue.cbcInitCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Rc2.AArch64.Fn.cbcInit
      (Spec.Rc2.cbcInitContract AArch64.abi 592) 32 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) cbcInitBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cbcInitScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Rc2.AArch64.InitResidue
