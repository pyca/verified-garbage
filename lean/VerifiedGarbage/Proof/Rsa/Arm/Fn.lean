module

public import VerifiedGarbage.Impl.Rsa.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.CkVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CvVerified
public import VerifiedGarbage.Proof.Rsa.Arm.RdTop
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreVerified
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA's key functions on ARMv7, as emitted

`Impl.Rsa.Arm.Fn` has each function with its cleanup; `Fn` below has the
theorem of each: it meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds.

`vg_rsa_check_key` and `vg_rsa_crt_values` have no frame
(`Arm.Scrub.verifiedScrubbed`, `Code.noFrames` by `lit_decide`). The others
zero the stack their contracts reserve (`Arm.Scrub.verifiedScrubbedF`): their
code makes no indirect call and its frames are within those bytes (`CodeOk`,
by `lit_decide`; of `vg_rsa_public_precompute`, which is an implementation's
code, the implementation's own, `CrtImpl.pcOk`), and their postconditions
read the memory on return only within their outputs (`PostOut`): the words
at `pre`, or the octets at `p` and `q`, as on x86 (`Proof/Rsa/X86/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Scrub

open VG.Arm VG.Arm.Scrub

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

theorem recoverPrimesDetOut (stack : Nat) :
    PostOut (Spec.Rsa.recoverPrimesDetContract abi stack) (Spec.Rsa.recoverPrimesDetSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [p, pLen, q, qLen, _, nLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.recoverPrimesDetSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, hpl, hql, -⟩ := hp
      have ep := bytesAt_of (n := (nLen.setWidth abi.ptrBits).toNat) hb.1
        (by rw [← hpl]; exact toNat_sw_le abi ScrubAbi.plain pLen)
      have eq := bytesAt_of (n := (nLen.setWidth abi.ptrBits).toNat) hb.2.1
        (by rw [← hql]; exact toNat_sw_le abi ScrubAbi.plain qLen)
      revert h
      generalize Option.map _ _ = v
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq] <;> exact id

/-! ## What the cleanup needs of the code -/

theorem frameOk_56 : FrameOk 56 := by decide

theorem frameOk_168 : FrameOk 168 := by decide

theorem checkKey_noFrames : Impl.Rsa.Arm.CheckKey.code.noFrames = true := by lit_decide

theorem checkKeyU_noFrames : Impl.Rsa.Arm.CheckKey.codeU.noFrames = true := by lit_decide

theorem crtValues_noFrames (um : Bool) : (Impl.Rsa.Arm.CrtValues.codeFor um).noFrames = true := by
  cases um <;> lit_decide

theorem recoverPrimesDet_ok (um : Bool) : CodeOk (Impl.Rsa.Arm.RecoverDet.codeFor um) 56 := by
  cases um <;> exact ⟨by lit_decide, by lit_decide⟩

theorem privatePrecompute_ok : CodeOk Impl.Bignum.Arm.PrivPreFn.code 168 := ⟨by lit_decide, by lit_decide⟩

theorem privatePrecomputeU_ok : CodeOk Impl.Bignum.Arm.PrivPreFn.codeU 168 := ⟨by lit_decide, by lit_decide⟩

end VG.Proof.Rsa.Arm.Scrub

namespace VG.Proof.Rsa.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub

/-- `vg_rsa_check_key`. -/
theorem checkKey : VerifiedScrubbed target Impl.Rsa.Arm.Fn.checkKey (Spec.Rsa.checkKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Rsa.checkKeyApi)
    { code := Impl.Rsa.Arm.CheckKey.code, verified := Proof.Rsa.Arm.CheckKey.check_key_verified }
    checkKey_noFrames

/-- `vg_rsa_check_key_umaal`. -/
theorem checkKeyU : VerifiedScrubbed target Impl.Rsa.Arm.Fn.checkKeyU (Spec.Rsa.checkKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Rsa.checkKeyApi)
    { code := Impl.Rsa.Arm.CheckKey.codeU, verified := Proof.Rsa.Arm.CheckKey.check_key_umaal_verified }
    checkKeyU_noFrames

/-- `vg_rsa_crt_values` (`um = false`) or `vg_rsa_crt_values_umaal`. -/
theorem crtValues [Proof.Rsa.Arm.Keys.InvLaw] (um : Bool) :
    VerifiedScrubbed target (Impl.Rsa.Arm.Fn.crtValues um) (Spec.Rsa.crtValuesContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.Rsa.crtValuesApi)
    { code := Impl.Rsa.Arm.CrtValues.codeFor um
      verified := Proof.Rsa.Arm.CrtValues.crt_values_for_verified um }
    (crtValues_noFrames um)

/-- `vg_rsa_recover_primes_det` (`um = false`) or
`vg_rsa_recover_primes_det_umaal`. -/
theorem recoverPrimesDet [Proof.Rsa.Arm.Keys.InvLaw] (um : Bool) :
    VerifiedScrubbed target (Impl.Rsa.Arm.Fn.recoverPrimesDet um) (Spec.Rsa.recoverPrimesDetContract abi 56) 32 :=
  verifiedScrubbedF (api := Spec.Rsa.recoverPrimesDetApi)
    { code := Impl.Rsa.Arm.RecoverDet.codeFor um
      verified := Proof.Rsa.Arm.Recover.recover_primes_det_for_verified um }
    (recoverPrimesDetOut _) (scrubSideF_of (recoverPrimesDet_ok um) frameOk_56 _)

/-- `vg_rsa_private_precompute`. -/
theorem privatePrecompute :
    VerifiedScrubbed target Impl.Rsa.Arm.Fn.privatePrecompute (Spec.Rsa.privatePrecomputeContract abi 168) 32 :=
  verifiedScrubbedF (api := Spec.Rsa.privatePrecomputeApi)
    { code := Impl.Bignum.Arm.PrivPreFn.code, verified := Proof.Bignum.Arm.privPre_verified }
    (privatePrecomputeOut _) (scrubSideF_of privatePrecompute_ok frameOk_168 _)

/-- `vg_rsa_private_precompute_umaal`. -/
theorem privatePrecomputeU :
    VerifiedScrubbed target Impl.Rsa.Arm.Fn.privatePrecomputeU (Spec.Rsa.privatePrecomputeContract abi 168) 32 :=
  verifiedScrubbedF (api := Spec.Rsa.privatePrecomputeApi)
    { code := Impl.Bignum.Arm.PrivPreFn.codeU, verified := Proof.Bignum.Arm.privPre_umaal_verified }
    (privatePrecomputeOut _) (scrubSideF_of privatePrecomputeU_ok frameOk_168 _)

/-- `vg_rsa_public_precompute`, of the implementation `v`. -/
theorem publicPrecompute (v : CrtImpl) :
    VerifiedScrubbed target (Impl.Rsa.Arm.Fn.publicPrecompute v.pc) (Spec.Rsa.publicPrecomputeContract abi 56) 32 :=
  verifiedScrubbedF (api := Spec.Rsa.publicPrecomputeApi) { code := v.pc, verified := v.pcVerified }
    (publicPrecomputeOut _) (scrubSideF_of v.pcOk frameOk_56 _)

end VG.Proof.Rsa.Arm.Fn
