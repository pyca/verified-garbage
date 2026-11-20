module

public import VerifiedGarbage.Impl.AesCcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-CCM on PPC64LE, without secret residue

`vg_aes_ccm_seal` and `vg_aes_ccm_open`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which clears the
volatile registers they may write and the whole 576-byte frame
(`withStackScratchArgs`) that holds their working space, the key schedule
and their callees' working space among it, which they do not wipe
themselves. Their postconditions read the memory on return only within the
data and the tag, as on AArch64 (`Proof/AesCcm/AArch64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract PPC64LE.abi stack) (Spec.Ccm.sealSig.retBits 64) :=
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
    PostOut (Spec.Ccm.openContract PPC64LE.abi stack) (Spec.Ccm.openSig.retBits 64) :=
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

/-! ## The functions as emitted -/

/-- `vg_aes_ccm_seal` as emitted (`Impl.AesCcm.PPC64LE.Fn.seal`) meets its
contract in constant time and returns without secret residue. -/
theorem seal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesCcm.PPC64LE.Fn.seal
      (Spec.Ccm.sealContract PPC64LE.abi 576) 0 :=
  verifiedScrubbed (api := Spec.Ccm.sealApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 576 2 Impl.AesCcm.PPC64LE.«seal»
      verified := Proof.AesCcm.seal_keyed seal_framed }
    576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (sealOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ccm_open` as emitted (`Impl.AesCcm.PPC64LE.Fn.open`) meets its
contract in constant time and returns without secret residue. -/
theorem open_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesCcm.PPC64LE.Fn.open
      (Spec.Ccm.openContract PPC64LE.abi 576) 32 :=
  verifiedScrubbed (api := Spec.Ccm.openApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 576 2 Impl.AesCcm.PPC64LE.«open»
      verified := Proof.AesCcm.open_keyed open_framed }
    576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (openOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesCcm.PPC64LE.Scrub
