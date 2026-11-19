module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecP
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndVerified

/-!
# RSAES-PKCS1-v1_5 on PPC64LE, without secret residue

`vg_rsa_pkcs1_decrypt_precomputed` and `vg_rsa_pkcs1_encrypt_random`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`),
which clears the volatile registers each may write and zeroes the stack
their frames used: decryption keeps the CRT's halves, the decoded message
and its callees' state in frames that it does not wipe itself. Their
postconditions read the memory on return only within `out` (and
decryption's `msg_len`, encryption's `tape`), given that `out` holds `n_len`
bytes, as on x86-64 and AArch64 (`Proof/Rsa/AArch64/Scrub.lean`).
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
    PostOut (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 64) :=
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

theorem writtenMsg_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsg m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsg m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsg, e, el] using h

theorem decryptPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      exact writtenMsg_of (e _ (by rw [toNat_sw]; exact hol.symm)) (wordsAt_of hb.2.1) h

/-! ## The registrations -/

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`. -/
def decryptPrecomputedReg : Registration Spec.RsaPkcs1Enc.decryptPrecomputedApi PPC64LE.target :=
  withScrub {
      code := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.codeP
      verified := Proof.RsaPkcs1Enc.PPC64LE.Dec.codeP_verified }
    (decryptPrecomputedOut _)

/-- `Spec.RsaPkcs1Enc.encryptRandomApi`. -/
def encryptRandomReg : Registration Spec.RsaPkcs1Enc.encryptRandomApi PPC64LE.target :=
  withScrub {
      code := Impl.RsaPkcs1Enc.PPC64LE.Random.code
      verified := Proof.RsaPkcs1Enc.PPC64LE.Rnd.code_verified }
    (encryptRandomOut _)

/-- Both are scrubbed: the side conditions of `withScrub` hold. -/
example : decryptPrecomputedReg.residue.isSome ∧ encryptRandomReg.residue.isSome := by
  decide

end VG.Proof.RsaPkcs1Enc.PPC64LE.Scrub
