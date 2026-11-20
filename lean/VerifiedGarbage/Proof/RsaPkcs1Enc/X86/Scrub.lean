module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSAES-PKCS1-v1_5 on x86 (32-bit), without secret residue

`vg_rsa_pkcs1_encrypt_random`, emitted with the zeroing of the stack its
contract reserves and the tail that clears the registers
(`Impl.RsaPkcs1Enc.X86.Fn.encryptRandom`), returns without secret residue
(`encryptRandom_scrubbed`). Its postcondition reads the memory on return only
within `out` and `tape`, given that `out` holds `n_len` bytes
(`X86.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub

/-! ## Postconditions -/

theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem encryptRandomOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen)
      rw [wordsAt_of hb.2.1]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      revert h2
      generalize (Spec.RsaPkcs1Enc.padSearch _ _).outcome = o
      match o with
      | .accepted _ => exact fun h2 hP => writtenRandom_of e' (h2 hP)
      | .entropy .. => simp only [e']; exact id
      | .exhausted => simp only [e']; exact id

/-! ## The function, with its cleanup -/

open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

/-- `vg_rsa_pkcs1_encrypt_random`, with the baseline public-key operation and
its cleanup, returns without secret residue. -/
theorem encryptRandom_scrubbed :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86.Fn.encryptRandom Proof.RsaPkcs1Enc.X86.Rnd.encName (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline))
      Proof.RsaPkcs1Enc.X86.Rnd.spec 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Enc.encryptRandomApi) {
      code := Impl.RsaPkcs1Enc.X86.Random.code Proof.RsaPkcs1Enc.X86.Rnd.encName
        (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline)
      verified := Proof.RsaPkcs1Enc.X86.Rnd.code_verified Proof.RsaPkcs1Enc.X86.Rnd.encName baseline
      spSafe := Proof.RsaPkcs1Enc.X86.Rnd.code_sp Proof.RsaPkcs1Enc.X86.Rnd.encName baseline }
    (encryptRandomOut _)

end VG.Proof.RsaPkcs1Enc.X86.Scrub
