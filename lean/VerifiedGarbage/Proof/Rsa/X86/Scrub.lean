module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Rsa.X86.Fn
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Instance
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimingW
public import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdDone
public import VerifiedGarbage.Proof.Rsa.X86.RtShape
public import VerifiedGarbage.Proof.Rsa.X86.BatchInstance
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Rsa.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
meta import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Instance
meta import VerifiedGarbage.Proof.Rsa.X86.CvVerified
meta import VerifiedGarbage.Proof.Rsa.X86.KcVerified
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimingW
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdDone
meta import VerifiedGarbage.Proof.Rsa.X86.RtShape
meta import VerifiedGarbage.Proof.Rsa.X86.BatchInstance

/-!
# RSA's key functions on x86 (32-bit), without secret residue

Each is emitted with its cleanup (`Impl.Rsa.X86.Fn`), and returns without
secret residue (`…_scrubbed`): `vg_rsa_recover_primes_det` and
`vg_rsa_check_key`, which call nothing and have no frame, followed by the
tail that clears the registers (`X86.Scrub.verifiedScrubbed`);
`vg_rsa_crt_values`, `vg_rsa_public_precompute` and
`vg_rsa_private_precompute` also by the zeroing of the stack their contracts
reserve (`X86.Scrub.verifiedScrubbedAll`). Their
postconditions read the memory on return only within their outputs
(`X86.Scrub.PostOut`): the words at `pre`, or the octets at `dp`, `dq` and
`qinv` (`bytesAt_of`, `wordsAt_of`). `vg_rsa_private_precompute` calls the
code of `vg_rsa_public_precompute` as the internal
`vg_rsa_public_precompute_core`, which is not scrubbed.

The lemmas they are built from are RSA's other functions' on x86 too
(`Proof/Rsa/X86/ScrubOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem publicPrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.publicPrecomputeContract abi stack) (Spec.Rsa.publicPrecomputeSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.publicPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have := toNat_sw_le abi ScrubAbi.plain preLen
      rw [wordsAt_of hb.1 (by omega_using [this])]
      exact h

theorem privatePrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.privatePrecomputeContract abi stack) (Spec.Rsa.privatePrecomputeSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have := toNat_sw_le abi ScrubAbi.plain preLen
      have e := wordsAt_of (n := (preLen.setWidth abi.ptrBits).toNat) hb.1 (by omega_using [this])
      revert h
      split
      · exact fun h => ⟨h.1, e.trans h.2⟩
      · exact fun h => ⟨h.1, e.trans h.2⟩

theorem crtValuesOut (stack : Nat) :
    PostOut (Spec.Rsa.crtValuesContract abi stack) (Spec.Rsa.crtValuesSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [dp, dpLen, dq, dqLen, qinv, qinvLen, _, _, _, pLen, _, qLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.crtValuesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, -, -, -, -, hdp, hqi, hdq, -⟩ := hp
      have ep := bytesAt_of hb.1 (hdp ▸ toNat_sw_le abi ScrubAbi.plain dpLen)
      have eq := bytesAt_of hb.2.1 (hdq ▸ toNat_sw_le abi ScrubAbi.plain dqLen)
      have ei := bytesAt_of hb.2.2.1 (hqi ▸ toNat_sw_le abi ScrubAbi.plain qinvLen)
      revert h
      generalize Option.map _ _ = v
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq, ei] <;> exact id

/-! ## The functions, with their cleanup -/

/-- `vg_rsa_recover_primes_det`, with its cleanup, returns without secret residue. -/
theorem recoverPrimesDet_scrubbed :
    VerifiedScrubbed target Impl.Rsa.X86.Fn.recoverPrimesDet (Spec.Rsa.recoverPrimesDetContract abi 96) 32 :=
  verifiedScrubbed (api := Spec.Rsa.recoverPrimesDetApi) {
    code := Impl.Rsa.X86.RecoverDetRt.code
    verified := Proof.Rsa.X86.Recover.verifiedD
    spSafe := Proof.Rsa.X86.RtShape.recoverDet_spSafe }

/-- `vg_rsa_check_key`, with its cleanup, returns without secret residue. -/
theorem checkKey_scrubbed :
    VerifiedScrubbed target Impl.Rsa.X86.Fn.checkKey (Proof.Rsa.X86.KeyCheck.contract true) 32 :=
  verifiedScrubbed (api := Spec.Rsa.checkKeyApi) {
    code := Impl.Rsa.X86.KeyCheckRt.code true
    verified := Proof.Rsa.X86.KeyCheck.verified true
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe true }

/-- `vg_rsa_crt_values`, with its cleanup, returns without secret residue. -/
theorem crtValues_scrubbed :
    VerifiedScrubbed target Impl.Rsa.X86.Fn.crtValues (Spec.Rsa.crtValuesContract abi 52) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.crtValuesApi)
    { code := Impl.Rsa.X86.CrtValuesRt.code
      verified := Proof.Rsa.X86.CrtValues.verified
      spSafe := Proof.Rsa.X86.RtShape.crtValues_spSafe }
    (crtValuesOut _)

/-- `vg_rsa_public_precompute`, with its cleanup, returns without secret residue. -/
theorem publicPrecompute_scrubbed :
    VerifiedScrubbed target Impl.Rsa.X86.Fn.publicPrecompute (Spec.Rsa.publicPrecomputeContract abi 96) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Impl.Bignum.X86.PrecomputeFn.code
      verified := Proof.Bignum.X86.precompute_verified }
    (publicPrecomputeOut _)

/-- `vg_rsa_private_precompute`, with its cleanup, returns without secret residue. -/
theorem privatePrecompute_scrubbed :
    VerifiedScrubbed target Impl.Rsa.X86.Fn.privatePrecompute
      (Spec.Rsa.privatePrecomputeContract abi Proof.Bignum.X86.PrivPre.stackBytes) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := Proof.Bignum.X86.PrivPre.ppCode
      verified := Proof.Bignum.X86.PrivPre.pp_verified
      spSafe := Proof.Bignum.X86.PrivPre.pp_spSafe }
    (privatePrecomputeOut _)

end VG.Proof.Rsa.X86.Scrub
