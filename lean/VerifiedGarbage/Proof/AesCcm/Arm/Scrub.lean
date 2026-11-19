module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.Arm.Frame
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCcm.Arm.Frame
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-CCM on ARMv7, without secret residue

`vg_aes_ccm_seal` and `vg_aes_ccm_open` keep their working space in a frame
within the 2608 bytes of stack their contracts reserve and make no indirect
call (evaluated by `lit_decide`), and their postconditions read the memory
on return only within their buffers (`Arm.Scrub.PostOut`, as on PPC64LE,
`Proof/AesCcm/PPC64LE/Scrub.lean`). Each is registered followed by a wipe of
that stack and by instructions that set the registers a callee may change,
but the result, and the flags to constants (`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal VG.Impl.AesCcm.Arm

theorem len_le (x : BitVec 64) : (BitVec.setWidth 32 x).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract Arm.abi stack) (Spec.Ccm.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.sealPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.sealPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (len_le _), bytesAt_of0 hb.2.2.2.2 (len_le _)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract Arm.abi stack) (Spec.Ccm.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.openPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.openPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le _)]
      exact h key hk

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_2608 : FrameOk 2608 := by decide

theorem seal_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal») = true := by
  lit_decide

theorem open_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») = true := by
  lit_decide

/-! ## The registrations -/

/-- `vg_aes_ccm_seal`. -/
def sealReg : Registration Spec.Ccm.sealApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»
      verified := Proof.AesCcm.seal_keyed Proof.AesCcm.Arm.seal_framed }
    seal_code.1 seal_code.2 frameOk_2608 (sealOut _) rfl

/-- `vg_aes_ccm_open`. -/
def openReg : Registration Spec.Ccm.openApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 «open»
      verified := Proof.AesCcm.open_keyed Proof.AesCcm.Arm.open_framed }
    open_code.1 open_code.2 frameOk_2608 (openOut _) rfl

end VG.Proof.AesCcm.Arm.Scrub
