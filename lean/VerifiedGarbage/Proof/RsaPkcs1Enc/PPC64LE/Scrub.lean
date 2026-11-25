module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomPublic
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecP
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndVerified
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSAES-PKCS1-v1_5 on PPC64LE, without secret residue

`vg_rsa_pkcs1_encrypt_random`, followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the volatile registers it
may write and zeroes the stack its frames used. Its postcondition reads the
memory on return only within `out` and `tape`, given that `out` holds
`n_len` bytes, as on x86-64 and AArch64 (`Proof/Rsa/AArch64/Scrub.lean`).
Decryption's is in `FrontScrub.lean`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Rsa.PPC64LE.Scrub

/-! ## Postconditions -/

theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem encryptRandomOut (stack : Nat) :
    PostOut (Proof.RsaPkcs1Enc.encryptRandomAskedContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw] at hol
      have e' := e _ hol.symm
      rw [wordsAt_of hb.2.1]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      revert h2
      generalize (Spec.RsaPkcs1Enc.padSearch _ _).outcome = o
      match o with
      | .accepted _ => exact fun h2 hP => writtenRandom_of e' (h2 hP)
      | .entropy .. => simp only [e']; exact id
      | .exhausted => simp only [e']; exact id

/-! ## The functions as emitted -/

/-- `vg_rsa_pkcs1_encrypt_random` as emitted
(`Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom`) meets its contract in constant
time and returns without secret residue. -/
theorem encryptRandom_asked :
    VerifiedScrubbed PPC64LE.target Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
      (Proof.RsaPkcs1Enc.encryptRandomAskedContract PPC64LE.abi Proof.RsaPkcs1Enc.PPC64LE.Rnd.rndStack) 32 :=
  verifiedScrubbedAll (api := Proof.RsaPkcs1Enc.encryptRandomAskedApi) {
      code := Impl.RsaPkcs1Enc.PPC64LE.Random.code
      verified := Proof.RsaPkcs1Enc.PPC64LE.Rnd.code_verified }
    3440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (encryptRandomOut _)
    (by dsimp only; lit_decide)

theorem encryptRandom_scrubbed :
    VerifiedScrubbed PPC64LE.target
      Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
      (Spec.RsaPkcs1Enc.encryptRandomContract PPC64LE.abi Proof.RsaPkcs1Enc.PPC64LE.Rnd.rndStack) 32 :=
  encryptRandom_imp (encryptRandom_asked) id

theorem encryptRandom_public :
    Spec.RsaPkcs1Enc.encryptRandomOut.Of PPC64LE.abi
      Impl.RsaPkcs1Enc.PPC64LE.Fn.encryptRandom
      (Spec.RsaPkcs1Enc.encryptRandomContract PPC64LE.abi Proof.RsaPkcs1Enc.PPC64LE.Rnd.rndStack) :=
  Proof.RsaPkcs1Enc.encryptRandom_public (encryptRandom_asked)

end VG.Proof.RsaPkcs1Enc.PPC64LE.Scrub
