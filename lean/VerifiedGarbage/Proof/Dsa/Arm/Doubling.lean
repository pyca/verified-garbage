module

public import VerifiedGarbage.Impl.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Omega

/-! # Counted modular doubling on ARMv7

The public counter stays in registers: `r1` across digit addition, then `r0`
across conditional subtraction. The arithmetic and memory bounds are those
of the existing addition and subtraction kernels.
-/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw wp_subs op2_reg op2_imm)

theorem countedDouble_parts_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Ws t base size ∧
      val32 t.mem base (resS n) (2 * n) =
        (val32 s.mem base (resS n) (2 * n) + val32 s.mem base (resS n) (2 * n)) % m ∧
      Outs base [(resS n, 8 * n), (tmpS n, 8 * n), (accS n, 4 * (8 * n + 2))] s.mem t.mem ∧
      Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 := by
  let M := contextMod n
  let acc := accS n
  let o := resS n
  let a := resS n
  let b := resS n
  have hs := h.ws
  have hn : 0 < M.n := h.n0
  have hL : MulLayD M size invO acc o a b :=
    context_lay h.size_le h.small (by decide) (by decide) (by decide)
  have hm : val32 s.mem base M.mo (words M) = m := h.modulus
  have hm0 : 0 < m := by have := h.gt_one; omega
  have hA : val32 s.mem base a (words M) < m := hv
  have hB : val32 s.mem base b (words M) < m := hv
  suffices H : WP isa (countedDouble n) s fun t => Ws t base size ∧
    val32 t.mem base o (words M) = (val32 s.mem base a (words M) + val32 s.mem base b (words M)) % m ∧
    Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
    Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 by
    simpa only [M, o, a, b, acc, contextMod, Impl.Mont.Arm.words,
      show 4 * (2 * n) = 8 * n by omega,
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega] using H
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hA hB ⊢
  unfold countedDouble
  refine WP.seq (WP.mono (VG.Arm.WP.gpr (addDigits_ok hs (M := M) (acc := acc) (a := a) (b := b) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact a_le) (by rw [hW]; exact b_le)
    (by rw [hD]; omega_using [acc16]) (by rw [hW]; exact a16) (by omega_using [b16])
    (by rw [hD, hW]; omega_using [sa]) (by rw [hD, hW]; omega_using [sb])) (r := .r1) (by
      simp [instrs, addDigits, ptrLoop, ptr, addDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t₀ ⟨⟨w₀, V₀, D₀, O₀, R₀⟩, C₀⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun t₁ U => WP.block_nil ?_)
  have w₁ := w₀.of_upd U (by decide)
  have V₁ := V₀
  have D₁ := D₀
  have O₁ := O₀
  rw [← U.mem] at V₁ D₁ O₁
  have R₁ := R₀.trans (U.rest (by decide : .r0 ∈ dclob))
  have C₁ : t₁.gpr .r0 = s.gpr .r1 := by rw [U.gpr, C₀]
  simp only [hD, hW] at V₁ D₁ O₁
  have hm₁ : val32 t₁.mem base M.mo W = m := by
    rw [O₁.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  refine WP.mono (VG.Arm.WP.gpr (csubD_ok w₁ (M := M) (src := acc) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so])
    (by rw [hW]; exact ot) (by rw [hW]; exact hm₁) hm0 (by rw [hD]; exact D₁) (by rw [hD, V₁]; omega_using [hA, hB])) (r := .r0) (by
      simp [instrs, csubD, ptrLoop, ptr, diffDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t ⟨⟨wt, V, O, R⟩, C⟩ => ⟨wt, ?_, ?_, R₁.trans R, C.trans C₁⟩
  · rw [hW] at V; rw [V, hD, V₁]
  · rw [hW] at O
    exact (Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * W + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)).trans (O.mono (by simp))

/-- One doubling keeps the context and carries the counter into `r0`. -/
theorem countedDouble_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 * val32 s.mem base (slot n 9) (2 * n) % m ∧
      t.gpr .r0 = s.gpr .r1 := by
  refine WP.mono (countedDouble_parts_ok h hv) fun t ⟨w, V, O, R, C⟩ => ?_
  have K : OpKeep n base 9 s t := ⟨R, O⟩
  exact ⟨h.keep (by decide) w K, K, by simpa only [resS, Nat.two_mul] using V, C⟩

structure DoubleInv (n m size k : Nat) (base : Addr) (s : State) (j : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 9) (2 * n) = 2 ^ j * val32 s.mem base (slot n 9) (2 * n) % m
  keep : OpKeep n base 9 s u
  count : u.gpr .r0 = BitVec.ofNat 32 (k - j)

theorem doubles_ok {n size m : Nat} {base : Addr} (k : Nat) {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m)
    (hk : k < 2 ^ 16) :
    WP isa (doubles n k) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 ^ k * val32 s.mem base (slot n 9) (2 * n) % m := by
  unfold doubles
  split
  · rename_i hz
    subst k
    exact WP.block_nil ⟨h, ⟨Rest.refl _ _, Outs.refl _ _ _⟩,
      by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv]⟩
  · rename_i hk0
    refine WP.seq (wp_movw fun t U => WP.block_nil ?_)
    have c : Context n m base size t := ⟨h.ws.of_upd U (by decide), h.size_le, h.small, h.n0,
      by rw [U.mem]; exact h.modulus, h.gt_one, by rw [U.mem]; exact h.inverse⟩
    have I0 : DoubleInv n m size k base s 0 t := ⟨c,
      by rw [U.mem, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv],
      ⟨U.rest (by decide), by rw [U.mem]; exact Outs.refl _ _ _⟩,
      by rw [U.gpr, Nat.sub_zero, movw_ofNat hk]⟩
    refine WP.loop (M := isa) (fun r u => ∃ j, r = k - j ∧ j < k ∧ DoubleInv n m size k base s j u)
      ?_ k t ⟨0, rfl, by omega, I0⟩
    rintro r u ⟨j, rfl, hj, I⟩
    refine WP.seq (wp_mov (op2_reg _ _) fun u₀ U₀ => WP.block_nil ?_)
    have c₀ : Context n m base size u₀ := ⟨I.ctx.ws.of_upd U₀ (by decide), I.ctx.size_le,
      I.ctx.small, I.ctx.n0, by rw [U₀.mem]; exact I.ctx.modulus, I.ctx.gt_one,
      by rw [U₀.mem]; exact I.ctx.inverse⟩
    have hm : 0 < m := by have := I.ctx.gt_one; omega
    refine WP.seq (WP.mono (countedDouble_ok c₀ (by rw [U₀.mem, I.val]; exact Nat.mod_lt _ hm))
      fun u₁ ⟨c₁, K₁, V₁, C₁⟩ => ?_)
    refine wp_subs (op2_imm (by decide)) fun u₂ U₂ Z₂ => WP.block_nil ?_
    have I' : DoubleInv n m size k base s (j + 1) u₂ := by
      refine ⟨⟨c₁.ws.of_upd U₂ (by decide), c₁.size_le, c₁.small, c₁.n0,
        by rw [U₂.mem]; exact c₁.modulus, c₁.gt_one, by rw [U₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_⟩
      · rw [U₂.mem, V₁, U₀.mem, I.val, Nat.mul_mod_mod, Nat.pow_succ]
        congr 1
        ac_rfl
      · refine ⟨((I.keep.rest.trans (U₀.rest (by decide))).trans K₁.rest).trans (U₂.rest (by decide)), ?_⟩
        rw [U₂.mem]
        exact I.keep.mem.trans (by rw [← U₀.mem]; exact K₁.mem)
      · rw [U₂.gpr, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega) (by omega)]
        congr 1
    have hz : u₂.z = decide (j + 1 = k) := by
      rw [Z₂, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega) (by omega),
        VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
      simp only [decide_eq_decide]
      omega
    by_cases hj1 : j + 1 = k
    · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj1]; rfl,
        I'.ctx, I'.keep, by rw [I'.val, hj1]⟩
    · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj1]; rfl,
        k - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

end VG.Proof.Dsa.Arm
