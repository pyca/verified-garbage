module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgPrecomputed
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTwo
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PKCS1-v1_5 on ARMv7, as emitted

`Impl.RsaPkcs1Sig.Arm.Fn` has each function with its cleanup; `Fn` below
has the theorem of each, for any implementation of the private CRT's
interface, whose precomputed public operation it calls: it
meets its contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds
(`Arm.Scrub.verifiedScrubbedAll`). What the cleanup needs of the code
(`CodeOk`) is proven once for any public operation, from what it states of
its own code (`CrtImpl.pdOk`), with the code around the call by
`lit_decide`. Their postconditions read the memory on return only within
`out`: verification not at all, recovery the recovered digest, signing the
signature, as on x86 and PPC64LE (`Proof/RsaPkcs1Sig/X86/Scrub.lean`,
`Proof/RsaPkcs1Sig/PPC64LE/Scrub.lean`).

Signing's 4664 bytes of stack are zeroed in two frames
(`Proof.Rsa.Arm.ScrubTwo.verifiedScrubbedAll2`): its frames' bytes, and the
private operation's (`privCodeP_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub

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
      have e' := bytesAt_of (n := (nLen.setWidth abi.ptrBits).toNat) hb.1
        (by rw [← hp.2.1]; exact toNat_sw_le abi ScrubAbi.plain outLen)
      revert h
      generalize Spec.RsaPkcs1Sig.signId _ _ _ _ _ _ _ _ _ = o
      cases o <;> simp only [Spec.Rsa.writtenOutcome, e'] <;> exact id

/-! ## What the cleanup needs of the code -/

/-- Signing's code, over the private operation `priv`. -/
theorem sign_ok {privN : String} {priv : Prog isa} (h : CodeOk priv 3488) :
    CodeOk (Impl.RsaPkcs1Sig.Arm.Sign.code true privN priv) 4664 := by
  refine wrap_codeOk (n := 3488) (F := 1120) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.ite ?_
    (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_))))))
  all_goals lit_decide

theorem frameOk_4080 : FrameOk 4080 := by decide

theorem frameOk_584 : FrameOk 584 := by decide

/-- Verification's code, over the public operation `pd`. -/
theorem verify_ok {pdName : String} {pd : Prog isa} (h : CodeOk pd 104) :
    CodeOk (Impl.RsaPkcs1Sig.Arm.Precomputed.code pdName pd) 2240 := by
  refine wrap_codeOk (n := 104) (F := 2080) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.ite ?_
    (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_)))))
  all_goals lit_decide

/-- Recovery's code, over the public operation `pd`. -/
theorem recover_ok {pdName : String} {pd : Prog isa} (h : CodeOk pd 104) :
    CodeOk (Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed.code pdName pd) 2240 := by
  refine wrap_codeOk (n := 104) (F := 2080) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.ite ?_
    (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_)))))
  all_goals lit_decide

theorem frameOk_2240 : FrameOk 2240 := by decide

end VG.Proof.RsaPkcs1Sig.Arm.Scrub

namespace VG.Proof.RsaPkcs1Sig.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.RsaPkcs1Sig.Arm.Scrub

/-- `vg_rsa_pkcs1_verify_precomputed`, calling `v`'s public operation. -/
theorem verifyPrecomputed (v : Proof.Rsa.Arm.CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Sig.Arm.Fn.verifyPrecomputed (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi 2240) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Sig.verifyPrecomputedApi)
    { code := Impl.RsaPkcs1Sig.Arm.Precomputed.code (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code
      verified := Proof.RsaPkcs1Sig.Arm.Vf.code_verified (Proof.Rsa.Arm.pdOfCrt v) }
    (verifyPrecomputedOut _) (scrubSideF_of (verify_ok v.pdOk) frameOk_2240 _)

/-- `vg_rsa_pkcs1_recover_precomputed`, calling `v`'s public operation. -/
theorem recoverPrecomputed (v : Proof.Rsa.Arm.CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Sig.Arm.Fn.recoverPrecomputed (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi 2240) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Sig.recoverPrecomputedApi)
    { code := Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed.code (Proof.Rsa.Arm.pdOfCrt v).name (Proof.Rsa.Arm.pdOfCrt v).code
      verified := Proof.RsaPkcs1Sig.Arm.Rc.code_verified (Proof.Rsa.Arm.pdOfCrt v) }
    (recoverPrecomputedOut _) (scrubSideF_of (recover_ok v.pdOk) frameOk_2240 _)

/-- `vg_rsa_pkcs1_sign_precomputed`, calling `vg_rsa_private_checked_precomputed`
over `v`. -/
theorem signPrecomputed (v : Proof.Rsa.Arm.CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Sig.Arm.Fn.signPrecomputed (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v))
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi 4664) 32 :=
  Proof.Rsa.Arm.ScrubTwo.verifiedScrubbedAll2 (a := 4080) (b := 584)
    (Proof.RsaPkcs1Sig.Arm.Sg.signPrecomputed_verified v) (sign_ok (Proof.Rsa.Arm.Scrub.privCodeP_ok v))
    frameOk_4080 frameOk_584 rfl (signPrecomputedOut _)

end VG.Proof.RsaPkcs1Sig.Arm.Fn
