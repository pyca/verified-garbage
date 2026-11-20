module

public import VerifiedGarbage.Impl.AesSiv.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Verified
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-SIV on PPC64LE, without secret residue

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which
clears the volatile registers they may write and the whole frame
(`withStackScratch`: 144 bytes for `init`, 480 for the others) that holds
their working space, the key schedules and their callees' working space
among it, which they do not wipe themselves. Their postconditions read the
memory on return only within the context, the data and `siv`, as on
AArch64 (`Proof/AesSiv/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Siv.initContract PPC64LE.abi stack) (Spec.Siv.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesSiv.initPostOut_local _)

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Siv.encryptContract PPC64LE.abi stack) (Spec.Siv.encryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.encryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2 i (by omega),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)]

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Siv.decryptContract PPC64LE.abi stack) (Spec.Siv.decryptSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.decryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth 64 len).toNat) fun i hi =>
        Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)
      rw [e]
      exact h key hk

/-! ## The functions as emitted -/

/-- `vg_aes_siv_init` as emitted (`Impl.AesSiv.PPC64LE.Fn.init`) meets its
contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesSiv.PPC64LE.Fn.init
      (Spec.Siv.initContract PPC64LE.abi 144) 0 :=
  verifiedScrubbed (api := Spec.Siv.initApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.AesSiv.PPC64LE.init
      verified := Proof.AesSiv.PPC64LE.init_framed }
    144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_siv_encrypt` as emitted (`Impl.AesSiv.PPC64LE.Fn.encrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem encrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesSiv.PPC64LE.Fn.encrypt
      (Spec.Siv.encryptContract PPC64LE.abi 480) 0 :=
  verifiedScrubbed (api := Spec.Siv.encryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 480 .r10 Impl.AesSiv.PPC64LE.encrypt
      verified := Proof.AesSiv.encrypt_keyed Proof.AesSiv.PPC64LE.encrypt_framed }
    480 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (encryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_siv_decrypt` as emitted (`Impl.AesSiv.PPC64LE.Fn.decrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem decrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.AesSiv.PPC64LE.Fn.decrypt
      (Spec.Siv.decryptContract PPC64LE.abi 480) 32 :=
  verifiedScrubbed (api := Spec.Siv.decryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 480 .r10 Impl.AesSiv.PPC64LE.decrypt
      verified := Proof.AesSiv.decrypt_keyed Proof.AesSiv.PPC64LE.decrypt_framed }
    480 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (decryptOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesSiv.PPC64LE.Scrub
