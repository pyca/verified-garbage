module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context

import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the conditional product

`exponentProduct n` multiplies the result by the base where the exponent's
low bit is set (`exponentProduct_ok`): the product is always computed, and
selected under the bit's mask.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr)

/-- A context, after code that changed only header bytes past `m'` and
registers outside `dclob`'s complement. -/
theorem Context.of_outside {n size m d len : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (w : Ws t base size) (O : Outside base d len s.mem t.mem) (hd : 4 ≤ d) (hl : d + len ≤ 256) :
    Context n m base size t := by
  have h0 := slot_header n 0
  have nw := h.ws.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have sz := h.size_le
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [O.val32 (by omega) (by simp only [stride] at b0; omega)]; exact h.modulus
  · rw [O.w32 (by simp only [invO]; omega) (by decide)]; exact h.inverse

/-- The memory the conditional product changes. -/
def productRanges (n : Nat) : List (Nat × Nat) :=
  [(maskO, 4), (slot n 10, 8 * n), (slot n 9, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem exponentProduct_ok {n size m y b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentProduct n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if w32 s.mem base (slot n 11) % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have hn := h.n0
  have hm0 : 0 < m := by have := h.gt_one; omega
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h11 := slot_header n 11
  have h8 : 8 ≤ size := by omega
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega
  unfold exponentProduct
  refine WP.seq (WP.mono (exponentMask_ok h.ws (n := n) (by simp only [expS, stride] at *; omega)
    (by simp only [expS, stride] at *; omega) (by omega)) fun s₁ ⟨w₁, M₁, O₁, R₁⟩ => ?_)
  have c₁ := h.of_outside w₁ O₁ (by decide) (by decide)
  have keep₁ (i : Nat) (hi : i < 12) : val32 s₁.mem base (slot n i) (2 * n) = val32 s.mem base (slot n i) (2 * n) := by
    have hd := slot_header n i
    have bd := slot_bound (n := n) hi
    exact O₁.val32 (by simp only [maskO]; omega) (by simp only [stride] at bd; omega)
  have hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by
    rw [keep₁ 8 (by decide), hb]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 10) (a := 9) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have mask₂ : w32 s₂.mem base maskO = w32 s₁.mem base maskO := by
    have h1 := slot_header n 1
    have h2 := slot_header n 2
    have h10 := slot_header n 10
    have := K₂.mem.val32 (d := maskO) (k := 1) (fun r hr => by
      simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [maskO] <;> omega) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine WP.seq (wp_ldr (by decide) (c₂.ws.ea12 (by simp only [maskO]; omega)) (c₂.ws.read (d := maskO) (n := 4)
    (by simp only [maskO]; omega)) fun s₃ u₃ => WP.block_nil ?_)
  have w₃ := c₂.ws.of_upd u₃ (by decide)
  have b9 := slot_bound (n := n) (i := 9) (by decide)
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have r3 : s₃.gpr .r3 = if decide (w32 s.mem base (slot n 11) % 2 = 1) = true then BitVec.allOnes 32 else 0 := by
    rw [u₃.gpr]
    apply BitVec.eq_of_toNat_eq
    show w32 s₂.mem base maskO = _
    rw [mask₂, M₁]
    simp only [decide_eq_true_eq, expS]
    rfl
  refine WP.mono (selectW_ok w₃ (k := 2 * n) (src := slot n 9) (tmp := slot n 10) (o := slot n 9) _ r3 (by omega)
    (by simp only [stride] at *; omega) (by simp only [stride] at *; omega) (by simp only [stride] at *; omega)
    (by simp only [stride] at *; omega) (by simp only [stride] at *; omega) (by simp only [stride] at *; omega)
    (.inl rfl) (.inl (by simp only [stride] at *; omega))) fun t ⟨wt, W, O, R⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := u₃.mem
  rw [m₃] at W O
  rw [show 4 * (2 * n) = 8 * n by omega] at O
  refine ⟨c₂.of_slot wt O (by decide), ?_, ?_, ?_⟩
  · have vp : val32 s₂.mem base (slot n 10) (2 * n) = y * b * 2 ^ (64 * n) % m := by
      have v := VG.Proof.Dsa.mont_product h.coprime (a := y) (b := b)
        (by rw [keep₁ 9 (by decide), hy, Nat.mod_mod]) (by rw [keep₁ 8 (by decide), hb, Nat.mod_mod]) V₂
      rwa [Nat.mod_eq_of_lt lt₂] at v
    have vy : val32 s₂.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m := by
      rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', keep₁ 9 (by decide), hy]
    by_cases hbit : w32 s.mem base (slot n 11) % 2 = 1
    · rw [val32_move (m := s₂.mem) (d := slot n 10) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_true, ↓reduceIte], vp, ite_eq_left hbit]
    · rw [val32_congr (m := s₂.mem) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_false, Bool.false_eq_true, ↓reduceIte], vy, ite_eq_right hbit]
  · have l1 := slot_le (n := n) (i := 1) (j := 9) (by decide)
    have l2 := slot_le (n := n) (i := 2) (j := 9) (by decide)
    have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega
    have l6 := slot_le (n := n) (i := 6) (j := 9) (by decide)
    have h1 := slot_header n 1
    refine ((Outs.of_outside O₁ (by simp [productRanges])).trans (K₂.mem.mono (by simp [productRanges]))).trans
      (Outs.of_outside O (by simp [productRanges]))
  · exact ((R₁.mono (by decide)).trans K₂.rest).trans ((u₃.rest (by decide)).trans (R.mono (by decide)))

end VG.Proof.Mont.Arm.Dyn
