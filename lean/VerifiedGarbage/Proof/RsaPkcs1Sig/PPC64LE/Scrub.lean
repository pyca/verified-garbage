module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignP
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PKCS1-v1_5 on PPC64LE, without secret residue

`vg_rsa_pkcs1_verify_precomputed`, `vg_rsa_pkcs1_recover_precomputed` and
`vg_rsa_pkcs1_sign_precomputed`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers each may write and zeroes the stack their frames used:
signing keeps the CRT's halves and the encoded message in frames that it
does not wipe itself. Their postconditions read the memory on return only
within `out`: verification not at all, recovery the recovered digest,
signing the signature, given that `out` holds `n_len` bytes, as on x86-64
(`Proof/Rsa/X86_64/Scrub.lean`, `Proof/RsaPkcs1Sig/X86_64/SignPrecomputed.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Rsa.PPC64LE.Scrub

/-! ## Postconditions -/

theorem verifyPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.verifyPrecomputedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem recoverPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.RsaPkcs1Sig.recoverPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := bytesAt_of hb.1
      exact fun hP H hH => written_of (by rw [toNat_sw]; exact e) (h hP H hH)

theorem signPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.signPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth abi.ptrBits).toNat =
          Spec.Rsa.bytesAt m₁ out (nLen.setWidth abi.ptrBits).toNat :=
        e _ (by rw [toNat_sw]; exact hol.symm)
      revert h
      generalize Spec.RsaPkcs1Sig.signId _ _ _ _ _ _ _ _ _ = o
      cases o <;> simp only [Spec.Rsa.writtenOutcome, e'] <;> exact id

/-! ## The registrations -/

/-- `Spec.RsaPkcs1Sig.verifyPrecomputedApi`. -/
def verifyPrecomputedReg : Registration Spec.RsaPkcs1Sig.verifyPrecomputedApi PPC64LE.target :=
  scrubOf {
      code := Impl.RsaPkcs1Sig.PPC64LE.Precomputed.code
      verified := Proof.RsaPkcs1Sig.PPC64LE.Ver.code_verified }
    2224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (verifyPrecomputedOut _)
    (by dsimp only; lit_decide)

/-- `Spec.RsaPkcs1Sig.recoverPrecomputedApi`. -/
def recoverPrecomputedReg : Registration Spec.RsaPkcs1Sig.recoverPrecomputedApi PPC64LE.target :=
  scrubOf {
      code := Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed.code
      verified := Proof.RsaPkcs1Sig.PPC64LE.Rec.code_verified }
    2224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (recoverPrecomputedOut _)
    (by dsimp only; lit_decide)

/-- `Spec.RsaPkcs1Sig.signPrecomputedApi`. -/
def signPrecomputedReg : Registration Spec.RsaPkcs1Sig.signPrecomputedApi PPC64LE.target :=
  scrubOf {
      code := Impl.RsaPkcs1Sig.PPC64LE.Sign.codeP
      verified := Proof.RsaPkcs1Sig.PPC64LE.Sign.codeP_verified }
    4608 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (signPrecomputedOut _)
    (by dsimp only; lit_decide)

end VG.Proof.RsaPkcs1Sig.PPC64LE.Scrub
