import VerifiedGarbage.Proof.Weierstrass.X86.PowerStep

/-! # Public-count repeated squaring in a fixed exponentiation chain -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem squareRun_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t : Nat} [NeZero m]
    {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n))) :
    ∀ n, n < 2 ^ 32 → WP isa (squareRun P F n) s fun u =>
      PowerState P base size m B (a * 2 ^ n) t u ∧ Keeps powClob s u ∧
      Unch base (powWx P wk) s.mem u.mem
  | 0, _ => by
    simp only [squareRun, Nat.pow_zero, Nat.mul_one]
    exact WP.block_nil ⟨I, Keeps.refl .., Unch.refl base (powWx P wk) s.mem⟩
  | n + 1, hn => by
    unfold squareRun
    refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
    let Inv := fun j u => PowerState P base size m B (a * 2 ^ (n + 1 - j)) t u ∧
      u.gpr .esi = BitVec.ofNat 32 j ∧ Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem
    refine countLoop_ok (Inv := Inv) (n := n + 1) ?_ ?_ (by omega) ?_
    · intro j v hj hjn hI
      obtain ⟨Iv, ev, Kv, Uv⟩ := hI
      refine WP.seq (wp_decCounter hj ev fun v₁ e₁ K₁ mem₁ => WP.block_nil ?_)
      have I₁ := Iv.regs K₁ (by decide) mem₁
      refine WP.seq (WP.mono (powerMul_ok I₁ hL hW hm hW.acc I₁.acc_lt I₁.acc_val)
        fun v₂ ⟨I₂, K₂, U₂⟩ => ?_)
      have ee : a * 2 ^ (n + 1 - j) + a * 2 ^ (n + 1 - j) = a * 2 ^ (n + 1 - (j - 1)) := by
        rw [show n + 1 - (j - 1) = (n + 1 - j) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
        omega
      rw [ee] at I₂
      have e₂ : v₂.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [K₂.1 _ esi_not_clob, e₁]
      refine wp_testCounter (by omega) e₂ fun u F hz => WP.block_nil ⟨?_, hz⟩
      refine ⟨I₂.regs (F.keeps []) (by decide) F.mem, by rw [F.gpr]; exact e₂,
        ((Kv.trans (K₁.mono (by decide))).trans (K₂.mono (by decide))).trans (F.keeps _), ?_⟩
      intro x hx
      rw [F.mem, U₂ x hx, mem₁]
      exact Uv x hx
    · intro u ⟨Iu, _, Ku, Uu⟩
      simp only [Nat.sub_zero] at Iu
      exact ⟨Iu, Ku, Uu⟩
    · refine ⟨?_, u₁.gpr, u₁.keeps.mono (by decide), ?_⟩
      · simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
        exact I.regs u₁.keeps (by decide) u₁.mem
      · rw [u₁.mem]; exact Unch.refl base (powWx P wk) s.mem

end VG.Proof.Weierstrass.X86
