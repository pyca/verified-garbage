module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
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
or not at all (`Arm.Scrub.PostOut`): each is registered followed by a wipe
of those bytes, and by instructions that set the registers a callee may
change, but the result, and the flags to constants (`Arm.Scrub.scrubRegF`).
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

theorem publicKey_noIcall (u : Bool) : noIcall (Impl.Ed448.Arm.PublicKey.code u) = true := by
  cases u <;> lit_decide

theorem publicKey_armStack (u : Bool) : armStack (Impl.Ed448.Arm.PublicKey.code u) ≤ 280 := by
  cases u <;> lit_decide

theorem signCached_noIcall (u : Bool) : noIcall (Impl.Ed448.Arm.SignCached.code u) = true := by
  cases u <;> lit_decide

theorem signCached_armStack (u : Bool) : armStack (Impl.Ed448.Arm.SignCached.code u) ≤ 280 := by
  cases u <;> lit_decide

theorem verify_noIcall (u : Bool) : noIcall (Impl.Ed448.Arm.Verify.code u) = true := by
  cases u <;> lit_decide

theorem verify_armStack (u : Bool) : armStack (Impl.Ed448.Arm.Verify.code u) ≤ 280 := by
  cases u <;> lit_decide

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

/-- `vg_ed448_public_key` with the field's multiplication `u`, as `suffix`, given the reference
comb's agreement with the specification. -/
def publicKeyReg (u : Bool) (suffix : String) (hl : Proof.Ed448.BaseCombOk) :
    Registration Spec.Ed448.publicKeyApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.Ed448.Arm.PublicKey.code u
      verified := PublicKey.publicKey_verified hl }
    (publicKey_armStack u) (publicKey_noIcall u) frameOk_280 (publicKeyOut _) rfl

/-- `vg_ed448_sign_cached` with the field's multiplication `u`, as `suffix`. -/
def signCachedReg (u : Bool) (suffix : String) (hl : Proof.Ed448.BaseCombOk) :
    Registration Spec.Ed448.signCachedApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.Ed448.Arm.SignCached.code u
      verified := SignCached.signCached_verified hl }
    (signCached_armStack u) (signCached_noIcall u) frameOk_280 (signCachedOut _) rfl

/-- `vg_ed448_verify` with the field's multiplication `u`, as `suffix`. -/
def verifyReg (u : Bool) (suffix : String) (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqCombOk) :
    Registration Spec.Ed448.verifyApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.Ed448.Arm.Verify.code u
      verified := Verify.verify_verified (Proof.Ed448.Arm.verifyEquation_ok hR hE)
        (Proof.Ed448.Arm.verifyEquation_ct hR) }
    (verify_armStack u) (verify_noIcall u) frameOk_280 (verifyOut _) rfl

end VG.Proof.Ed448.Arm.Scrub
