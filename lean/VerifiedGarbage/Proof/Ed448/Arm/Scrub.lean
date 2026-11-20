module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Ed448.CombFacts
public import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Sha3.Arm.Absorb
public import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.Arm.Scrub
import VerifiedGarbage.Proof.Ed448.Arm.BaseLit
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
meta import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified
meta import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.X448.Arm.Scrub
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseLit
meta import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed448 on ARMv7, without secret residue

Ed448's public functions, with either multiplication of the field
(`Proof/Variants/Curve448Field/Arm.lean`), call their callees from frames of
280 bytes, and their postconditions read the memory on return only at `out`,
or not at all (`Arm.Scrub.PostOut`): each is emitted followed by a wipe of
those bytes, and by instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Ed448.Arm.Fn`). The code's
shape is the same with either multiplication but where it is chosen
(`Proof.X448.Arm.Scrub.ops_shape`), so what the cleanup needs of it is proven
once for both, with the Keccak functions' evaluated once (`lit_decide`); `Fn`
has the theorem of each, which its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- The `n` octets at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) :
    Spec.Ed448.bytesAt m₂ o n = Spec.Ed448.bytesAt m₁ o n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Proof.X448.Arm.Scrub.contains_of (by omega_using [this, hN]))).symm

theorem frameOk_280 : FrameOk 280 := by decide

theorem absorb_codeOk : CodeOk Impl.Sha3.Arm.Stream.absorb 0 := by lit_decide

theorem pad_codeOk : CodeOk Impl.Sha3.Arm.Stream.pad 0 := by lit_decide

theorem squeeze_codeOk : CodeOk Impl.Sha3.Arm.Stream.squeeze 0 := by lit_decide

theorem publicKey_codeOk (u : Bool) : CodeOk (Impl.Ed448.Arm.PublicKey.code u) 280 := by
  obtain ⟨a1, a2⟩ := absorb_codeOk
  obtain ⟨p1, p2⟩ := pad_codeOk
  obtain ⟨q1, q2⟩ := squeeze_codeOk
  rw [Nat.le_zero] at a1 p1 q1
  simp only [CodeOk,
    Impl.Ed448.Arm.PublicKey.zeroState, Impl.Ed448.Arm.PublicKey.hash, Impl.Ed448.Arm.PublicKey.prune,
    Impl.Ed448.Arm.PublicKey.body, Impl.Ed448.Arm.PublicKey.code, Impl.Ed448.Arm.baseBits,
    Impl.Ed448.Arm.combStep, Impl.Ed448.Arm.combLoop, Impl.Ed448.Arm.baseEncode,
    Impl.Ed448.Arm.scalarBase, Impl.X448.Arm.callFn, Impl.X448.Arm.Op.code, Impl.X448.Arm.ops,
    Impl.X448.Arm.sqn, Impl.X448.Arm.invert, Impl.Ed25519.Arm.Whole.callWith,
    Impl.Ed25519.Arm.Whole.wrap, armStack, noIcall, a1, a2, p1, p2, q1, q2,
    (Proof.X448.Arm.Scrub.ops_shape _ _).2.1, (Proof.X448.Arm.Scrub.ops_shape _ _).2.2,
    (Proof.X448.Arm.Scrub.mulFn_shape _).2.1, (Proof.X448.Arm.Scrub.mulFn_shape _).2.2, Bool.and_self,
    Nat.max_self, List.length_cons, List.length_nil]
  decide

theorem signCached_codeOk (u : Bool) : CodeOk (Impl.Ed448.Arm.SignCached.code u) 280 := by
  obtain ⟨a1, a2⟩ := absorb_codeOk
  obtain ⟨p1, p2⟩ := pad_codeOk
  obtain ⟨q1, q2⟩ := squeeze_codeOk
  rw [Nat.le_zero] at a1 p1 q1
  simp only [CodeOk,
    Impl.Ed448.Arm.reduce114, Impl.Ed448.Arm.reduce57, Impl.Ed448.Arm.scalarReduce,
    Impl.Ed448.Arm.reduceArg, Impl.Ed448.Arm.inputs, Impl.Ed448.Arm.product,
    Impl.Ed448.Arm.reduceProduct, Impl.Ed448.Arm.scalarMulAdd, Impl.Ed448.Arm.baseBits,
    Impl.Ed448.Arm.combStep, Impl.Ed448.Arm.combLoop, Impl.Ed448.Arm.baseEncode,
    Impl.Ed448.Arm.scalarBase, Impl.Ed448.Arm.Shake.zeroState, Impl.Ed448.Arm.Shake.absorb,
    Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, Impl.Ed448.Arm.SignCached.seedHash,
    Impl.Ed448.Arm.SignCached.prune, Impl.Ed448.Arm.SignCached.nonceHash,
    Impl.Ed448.Arm.SignCached.chalHash, Impl.Ed448.Arm.SignCached.body, Impl.Ed448.Arm.SignCached.code,
    Impl.X448.Arm.callFn, Impl.X448.Arm.Op.code, Impl.X448.Arm.ops, Impl.X448.Arm.sqn,
    Impl.X448.Arm.invert, Impl.Ed25519.Arm.Whole.callWith, Impl.Ed25519.Arm.Whole.wrap, armStack,
    noIcall, a1, a2, p1, p2, q1, q2, (Proof.X448.Arm.Scrub.ops_shape _ _).2.1,
    (Proof.X448.Arm.Scrub.ops_shape _ _).2.2, (Proof.X448.Arm.Scrub.mulFn_shape _).2.1,
    (Proof.X448.Arm.Scrub.mulFn_shape _).2.2, Bool.and_self, Nat.max_self, List.length_cons,
    List.length_nil]
  decide

theorem verify_codeOk (u : Bool) : CodeOk (Impl.Ed448.Arm.Verify.code u) 280 := by
  obtain ⟨a1, a2⟩ := absorb_codeOk
  obtain ⟨p1, p2⟩ := pad_codeOk
  obtain ⟨q1, q2⟩ := squeeze_codeOk
  rw [Nat.le_zero] at a1 p1 q1
  simp only [CodeOk,
    Impl.Ed448.Arm.reduce114, Impl.Ed448.Arm.scalarReduce, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze,
    Impl.Ed448.Arm.Verify.hash, Impl.Ed448.Arm.Verify.body, Impl.Ed448.Arm.Verify.code,
    Impl.Ed448.Arm.root, Impl.Ed448.Arm.decode, Impl.Ed448.Arm.recBit, Impl.Ed448.Arm.vrecode,
    Impl.Ed448.Arm.vtableInit, Impl.Ed448.Arm.vtableStep, Impl.Ed448.Arm.vtable, Impl.Ed448.Arm.vaddIf,
    Impl.Ed448.Arm.vcombIf, Impl.Ed448.Arm.vdoubleAdd, Impl.Ed448.Arm.vstep, Impl.Ed448.Arm.vloop,
    Impl.Ed448.Arm.vbits, Impl.Ed448.Arm.vdouble, Impl.Ed448.Arm.vdecodeBody, Impl.Ed448.Arm.vdecode,
    Impl.Ed448.Arm.vcmp, Impl.Ed448.Arm.vfinish, Impl.Ed448.Arm.vbefore, Impl.Ed448.Arm.vafter,
    Impl.Ed448.Arm.verifyEquation, Impl.X448.Arm.fn, Impl.X448.Arm.subFn, Impl.X448.Arm.callFn,
    Impl.X448.Arm.Op.code, Impl.X448.Arm.ops, Impl.X448.Arm.sqn, Impl.Ed25519.Arm.Whole.callWith,
    Impl.Ed25519.Arm.Whole.wrap, armStack, noIcall, a1, a2, p1, p2, q1, q2,
    (Proof.X448.Arm.Scrub.ops_shape _ _).2.1, (Proof.X448.Arm.Scrub.ops_shape _ _).2.2,
    (Proof.X448.Arm.Scrub.mulFn_shape _).2.1, (Proof.X448.Arm.Scrub.mulFn_shape _).2.2, Bool.and_self,
    Nat.max_self, List.length_cons, List.length_nil]
  decide

theorem publicKeyOut (stack : Nat) :
    PostOut (Spec.Ed448.publicKeyContract abi stack) (Spec.Ed448.publicKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun
    | [out, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ed448.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (Nat.le_refl 57)]
      exact h

theorem signCachedOut (stack : Nat) :
    PostOut (Spec.Ed448.signCachedContract abi stack) (Spec.Ed448.signCachedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun
    | [out, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ed448.signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (Nat.le_refl 114)]
      exact h

theorem verifyOut (stack : Nat) :
    PostOut (Spec.Ed448.verifyContract abi stack) (Spec.Ed448.verifySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _], m, m₁, m₂, r, _, _, h => by
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      exact h

end VG.Proof.Ed448.Arm.Scrub

namespace VG.Proof.Ed448.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ed448_public_key`, with either multiplication of the field. -/
theorem publicKey (u : Bool) :
    VerifiedScrubbed target (Impl.Ed448.Arm.Fn.publicKey u) (Spec.Ed448.publicKeyContract abi 280) 0 :=
  verifiedScrubbedAll (api := Spec.Ed448.publicKeyApi)
    { code := Impl.Ed448.Arm.PublicKey.code u, verified := PublicKey.publicKey_verified Proof.Ed448.baseComb_ok }
    (Scrub.publicKeyOut _) (scrubSideF_of (Scrub.publicKey_codeOk u) Scrub.frameOk_280 _)

/-- `vg_ed448_sign_cached`, with either multiplication of the field. -/
theorem signCached (u : Bool) :
    VerifiedScrubbed target (Impl.Ed448.Arm.Fn.signCached u) (Spec.Ed448.signCachedContract abi 280) 0 :=
  verifiedScrubbedAll (api := Spec.Ed448.signCachedApi)
    { code := Impl.Ed448.Arm.SignCached.code u
      verified := SignCached.signCached_verified Proof.Ed448.baseComb_ok }
    (Scrub.signCachedOut _) (scrubSideF_of (Scrub.signCached_codeOk u) Scrub.frameOk_280 _)

/-- `vg_ed448_verify`, with either multiplication of the field. -/
theorem verify (u : Bool) :
    VerifiedScrubbed target (Impl.Ed448.Arm.Fn.verify u) (Spec.Ed448.verifyContract abi 280) 32 :=
  verifiedScrubbedAll (api := Spec.Ed448.verifyApi)
    { code := Impl.Ed448.Arm.Verify.code u
      verified := Verify.verify_verified
        (Proof.Ed448.Arm.verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEqComb_ok)
        (Proof.Ed448.Arm.verifyEquation_ct Proof.Ed448.recover_ok) }
    (Scrub.verifyOut _) (scrubSideF_of (Scrub.verify_codeOk u) Scrub.frameOk_280 _)

end VG.Proof.Ed448.Arm.Fn
