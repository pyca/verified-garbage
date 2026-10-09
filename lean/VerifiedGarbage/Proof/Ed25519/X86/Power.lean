import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.X25519.X86.Field32.Call

/-! The shared addition chain, a call of `vg_gf25519_r32_pow250`
(`power250_ok`), computes the inversion and square-root powers with a few
squarings and a product each (`invert_ok`, `rootPower_ok`). -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519 (pw pw_mul pw_one sqn_pw pow_pw)

theorem power250_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa power250 s fun t => IKeep base s t ∧
      env t.mem base 15 = pw (env s.mem base 2) (2 ^ 250 - 1) ∧
      env t.mem base 14 = pw (env s.mem base 2) 11 ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  have hfit := hs.fit
  refine WP.mono (VG.Proof.X25519.X86.Field32.pow250Call_ok hs) fun t ⟨hk, hf, h1, h0⟩ =>
    ⟨⟨hk.edi, hk.esp, hk.rd, hk.wr, frameWidenS hf hfit (by decide) (by decide) (by decide)⟩, h1, h0,
      fun i hi => ?_⟩
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1s hs hf (by decide) (by simp only [offset]; omega) (.inl (by simp only [offset]; omega))

/-- The chain's tail for the inversion: five squarings, and `z^11`. -/
theorem invert_tail (z : Spec.X25519.Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 5 * pw z 11 = VG.Proof.X25519.invert z := by
  rw [VG.Proof.X25519.invert_eq, pow_pw, sqn_pw, pw_mul]
  exact congrArg (pw z) (by decide)

/-- The chain's tail for the square root: two squarings, and `z`. -/
theorem root_tail (z : Spec.X25519.Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 2 * z = VG.Proof.Ed25519.rootPower z := by
  have e := pw_mul z ((2 ^ 250 - 1) * 2 ^ 2) 1
  rw [pw_one] at e
  rw [VG.Proof.Ed25519.rootPower_eq, pow_pw, sqn_pw, e]
  exact congrArg (pw z) (by decide)

theorem invert_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa invert s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  refine WP.seq (WP.mono (power250_ok hs) fun t ⟨kt, h15, h14, hlow⟩ => ?_)
  have h : ISpec base _ _ := (sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 15 15 14 ⟨by decide, by decide⟩)
  refine WP.mono (h t (kt.ctx hs)) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, fun i hi => ?_⟩
  · rw [eu]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (14 : Slot) ≠ 15 by decide)]
    rw [h15, h14, invert_tail]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [eu]
    simp only [opMul, opSqn, Function.update_of_ne h15]
    exact hlow i hi

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa Impl.Ed25519.X86.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  refine WP.seq (WP.mono (power250_ok hs) fun t ⟨kt, h15, _, hlow⟩ => ?_)
  have h : ISpec base _ _ := (sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 15 15 2 ⟨by decide, by decide⟩)
  refine WP.mono (h t (kt.ctx hs)) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, fun i hi => ?_⟩
  · rw [eu]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (2 : Slot) ≠ 15 by decide)]
    rw [h15, hlow 2 (by decide), root_tail]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [eu]
    simp only [opMul, opSqn, Function.update_of_ne h15]
    exact hlow i hi

end VG.Proof.Ed25519.X86
