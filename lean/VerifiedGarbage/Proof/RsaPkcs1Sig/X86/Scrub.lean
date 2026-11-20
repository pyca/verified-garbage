module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Fn
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyVerified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Fn
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyVerified
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSASSA-PKCS1-v1_5 on x86 (32-bit), without secret residue

`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`,
each emitted with the zeroing of the stack its contract reserves and the
tail that clears the registers (`Impl.RsaPkcs1Sig.X86.Fn`), return without
secret residue (`…_scrubbed`). Their
postconditions read the memory on return only within `out`: verification
not at all, recovery the recovered digest (`X86.Scrub.PostOut`).
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

/-! ## The functions, with their cleanup -/

open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

/-- `vg_rsa_pkcs1_verify_precomputed`, with the baseline public-key operation
and its cleanup, returns without secret residue. -/
theorem verifyPrecomputed_scrubbed :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.X86.Fn.verifyPrecomputed baseline.name baseline.code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi Proof.RsaPkcs1Sig.X86.Ver.verifyStack) 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Sig.verifyPrecomputedApi) {
      code := Impl.RsaPkcs1Sig.X86.Verify.code baseline.name baseline.code
      verified := Proof.RsaPkcs1Sig.X86.Ver.verify_verified baseline
      spSafe := Proof.RsaPkcs1Sig.X86.Ver.code_sp baseline }
    (verifyPrecomputedOut _)

/-- `vg_rsa_pkcs1_recover_precomputed`, with the baseline public-key operation
and its cleanup, returns without secret residue. -/
theorem recoverPrecomputed_scrubbed :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.X86.Fn.recoverPrecomputed baseline.name baseline.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi Proof.RsaPkcs1Sig.X86.Rcv.recoverStack) 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Sig.recoverPrecomputedApi) {
      code := Impl.RsaPkcs1Sig.X86.Recover.code baseline.name baseline.code
      verified := Proof.RsaPkcs1Sig.X86.Rcv.recover_verified baseline
      spSafe := Proof.RsaPkcs1Sig.X86.Rcv.code_sp baseline }
    (recoverPrecomputedOut _)

end VG.Proof.RsaPkcs1Sig.X86.Scrub
