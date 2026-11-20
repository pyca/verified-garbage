module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Verified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignScrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Fn
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Verified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignScrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSASSA-PKCS1-v1_5 on x86 (32-bit), without secret residue

`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`,
each followed by the zeroing of the stack its contract reserves and the
tail that clears the registers (`X86.Scrub.scrubFOf`). Their
postconditions read the memory on return only within `out`: verification
not at all, recovery the recovered digest (`X86.Scrub.PostOut`).

`vg_rsa_pkcs1_sign_precomputed`, generic over the implementation of the
private-key operation, is emitted with its cleanup
(`Impl.RsaPkcs1Sig.X86.Fn.signPrecomputed`), which returns without secret
residue whatever the implementation (`signPrecomputed_scrubbed`), from what
its cleanup needs of its code (`SignScrub.sign_scrub`). Its postcondition
reads the memory on return only within `out`, given that `out` holds
`n_len` bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub

/-! ## Postconditions -/

theorem verifyPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.verifyPrecomputedSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem recoverPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.RsaPkcs1Sig.recoverPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      exact fun hP H hH => written_of (bytesAt_of hb.1 (toNat_sw_le abi ScrubAbi.plain outLen)) (h hP H hH)

theorem signPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.signPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits 32) :=
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
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen)
      revert h
      generalize Spec.RsaPkcs1Sig.signId _ _ _ _ _ _ _ _ _ = o
      cases o <;> simp only [Spec.Rsa.writtenOutcome, e'] <;> exact id

/-! ## The registrations -/

open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

/-- `Spec.RsaPkcs1Sig.verifyPrecomputedApi`, with the baseline public-key operation. -/
def verifyPrecomputedReg : Registration Spec.RsaPkcs1Sig.verifyPrecomputedApi X86.target :=
  scrubFOf {
      code := Impl.RsaPkcs1Sig.X86.Verify.code baseline.name baseline.code
      verified := Proof.RsaPkcs1Sig.X86.Ver.verify_verified baseline
      spSafe := Proof.RsaPkcs1Sig.X86.Ver.code_sp baseline }
    (verifyPrecomputedOut _)

/-- `Spec.RsaPkcs1Sig.recoverPrecomputedApi`, with the baseline public-key operation. -/
def recoverPrecomputedReg : Registration Spec.RsaPkcs1Sig.recoverPrecomputedApi X86.target :=
  scrubFOf {
      code := Impl.RsaPkcs1Sig.X86.Recover.code baseline.name baseline.code
      verified := Proof.RsaPkcs1Sig.X86.Rcv.recover_verified baseline
      spSafe := Proof.RsaPkcs1Sig.X86.Rcv.code_sp baseline }
    (recoverPrecomputedOut _)

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline) in
/-- `vg_rsa_pkcs1_sign_precomputed`, with its cleanup, returns without secret
residue, whatever the implementation `v` of the private-key operation. -/
theorem signPrecomputed_scrubbed (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Sig.X86.Fn.signPrecomputed (Proof.RsaPkcs1Sig.X86.Sgn.privNameP v) (privCodeP v crtPBaseline))
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi Proof.RsaPkcs1Sig.X86.Sgn.sigStack) 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Sig.signPrecomputedApi)
    { code := Impl.RsaPkcs1Sig.X86.Sign.code (Proof.RsaPkcs1Sig.X86.Sgn.privNameP v) (privCodeP v crtPBaseline)
        Impl.RsaPkcs1Sig.X86.Sign.callArgsP
      verified := Proof.RsaPkcs1Sig.X86.Sgn.signPrecomputed_verified v
      spSafe := Proof.RsaPkcs1Sig.X86.Sgn.codeP_sp v crtPBaseline }
    (signPrecomputedOut _) (hs := Proof.RsaPkcs1Sig.X86.SignScrub.sign_scrub v)

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline) in
/-- `vg_rsa_pkcs1_sign_precomputed`, with its cleanup, writes `esp` only by its frames. -/
theorem signPrecomputed_spSafe (v : CrtImpl) :
    (Impl.RsaPkcs1Sig.X86.Fn.signPrecomputed (Proof.RsaPkcs1Sig.X86.Sgn.privNameP v)
      (privCodeP v crtPBaseline)).all (fun i => !isa.writesSp i) = true :=
  scrubF_all (Proof.RsaPkcs1Sig.X86.Sgn.codeP_sp v crtPBaseline)

end VG.Proof.RsaPkcs1Sig.X86.Scrub
