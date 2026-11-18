module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# AES-CCM on RISC-V, without secret residue

`vg_aes_ccm_seal` and `vg_aes_ccm_open`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used, the working space of its callees with it. Their
postconditions read the memory on return only within the data and the tag
(`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/AesCcm/X86_64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesCcm.RISCV64

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract RISCV64.abi stack) (Spec.Ccm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (by simp), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract RISCV64.abi stack) (Spec.Ccm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Ccm.sealApi`. -/
def sealReg : Registration Spec.Ccm.sealApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«seal»
      verified := Proof.AesCcm.seal_keyed seal_framed }
    (sealOut _)

/-- `Spec.Ccm.openApi`. -/
def openReg : Registration Spec.Ccm.openApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«open»
      verified := Proof.AesCcm.open_keyed open_framed }
    (openOut _)

end VG.Proof.AesCcm.RISCV64.Scrub
