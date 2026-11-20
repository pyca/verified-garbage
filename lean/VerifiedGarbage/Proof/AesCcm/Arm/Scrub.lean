module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.AesCcm.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.Arm.Frame
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.AesCcm.Arm.Fn
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
`Proof/AesCcm/PPC64LE/Scrub.lean`). Each is emitted followed by a wipe of
that stack and by instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.AesCcm.Arm.Fn`), and `Fn` below states
that it returns without secret residue (`Arm.Scrub.verifiedScrubbedF`), which
is what its registration binds.
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
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal») 2608 := by
  lit_decide

theorem open_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») 2608 := by
  lit_decide

end VG.Proof.AesCcm.Arm.Scrub

namespace VG.Proof.AesCcm.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal VG.Impl.AesCcm.Arm

/-- `vg_aes_ccm_seal`. -/
theorem «seal» : VerifiedScrubbed target Impl.AesCcm.Arm.Fn.«seal» (Spec.Ccm.sealContract abi 2608) 0 :=
  verifiedScrubbedF (api := Spec.Ccm.sealApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«seal»
      verified := Proof.AesCcm.seal_keyed Proof.AesCcm.Arm.seal_framed }
    (Scrub.sealOut _) (scrubSideF_of Scrub.seal_code Scrub.frameOk_2608 _)

/-- `vg_aes_ccm_open`. -/
theorem «open» : VerifiedScrubbed target Impl.AesCcm.Arm.Fn.«open» (Spec.Ccm.openContract abi 2608) 32 :=
  verifiedScrubbedF (api := Spec.Ccm.openApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«open»
      verified := Proof.AesCcm.open_keyed Proof.AesCcm.Arm.open_framed }
    (Scrub.openOut _) (scrubSideF_of Scrub.open_code Scrub.frameOk_2608 _)

end VG.Proof.AesCcm.Arm.Fn
