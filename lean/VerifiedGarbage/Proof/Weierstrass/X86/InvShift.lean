import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftTail

/-! # Shifting the signed result of a divstep matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shrRows_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) :
    ∀ j, j + 1 ≤ n → WP isa (.block ((List.range j).flatMap (shrStep dst src))) s fun u =>
      val32 u.mem base dst j = val32 s.mem base src (j + 1) / 2 ^ 30 % 2 ^ (32 * j) ∧
      Keeps [.eax, .ebx] s u ∧ Outside base dst (4 * j) s.mem u.mem
  | 0, _ => WP.block_nil ⟨by simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
      Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrRows_ok hs ha hd sep j (by omega)) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_
    refine WP.mono (shrStep_ok (hs.of_keeps K₁ (by decide)) (by omega) (by omega))
      fun u ⟨V₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
    · rw [val32_succ, O₂.val32 (by omega) (by omega), V₁, V₂,
        O₁.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega),
        val32_succ s.mem base src (j + 1), val32_succ s.mem base src j, pow32_succ,
        Nat.mul_comm (2 ^ 32) (2 ^ (32 * j))]
      exact (shr_arith32 j _ _ _ (val32_lt _ _ _ _)).symm
    · intro x hx
      rw [O₂ x (by omega), O₁ x (by omega)]

def sext32 (m : Mem) (base : Addr) (src n : Nat) : Nat :=
  val32 m base src n + 2 ^ (32 * n) *
    (if 2 ^ 31 ≤ w32 m base (src + 4 * (n - 1)) then 2 ^ 32 - 1 else 0)

theorem shr30_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (hn : 1 ≤ n) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) :
    WP isa (.block (shr30 dst src n)) s fun u =>
      val32 u.mem base dst n = sext32 s.mem base src n / 2 ^ 30 % 2 ^ (32 * n) ∧
      Keeps [.eax, .ebx, .ecx] s u ∧ Outside base dst (4 * n) s.mem u.mem := by
  have hwrap := hs.nowrap
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [shr30, Nat.add_sub_cancel]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (shrRows_ok hs ha hd sep j (Nat.le_refl _)) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)))
  refine WP.mono (maskOf_ok (hs.of_keeps K₁ (by decide)) (by omega)) fun s₂ ⟨C₂, K₂, M₂⟩ => ?_
  have K : Keeps [.eax, .ebx, .ecx] s s₂ :=
    (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_sc hs₂ (by omega)) fun s₃ U₃ _ => ?_
  refine wp_movS rfl fun s₄ U₄ _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ecx] s₂ s₄ :=
    (U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))
  refine WP.mono (shrTail_ok (hs₂.of_keeps K' (by decide)) (by omega)) fun u ⟨V, K₅, O₅⟩ =>
    ⟨?_, (K.trans K').trans (K₅.mono (by decide)), ?_⟩
  · have W : w32 s₁.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O₁.w32 (by omega) (by omega)
    rw [val32_succ, O₅.val32 (by omega) (by omega), U₄.mem, U₃.mem, M₂, V₁,
      V, U₄.other _ (by decide), U₃.gpr, U₄.gpr, U₃.other _ (by decide), C₂, M₂, W]
    simp only [w32] at W
    rw [W]
    have E : (if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then BitVec.allOnes 32 else 0).toNat =
        if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then 2 ^ 32 - 1 else 0 := by
      split <;> rfl
    rw [E, sext32, Nat.add_sub_cancel, val32_succ s.mem base src j, pow32_succ,
      Nat.mul_comm (2 ^ 32) (2 ^ (32 * j))]
    simpa only [Nat.mul_assoc] using (shr_arith32 j (val32 s.mem base src j)
      (w32 s.mem base (src + 4 * j))
      (if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then 2 ^ 32 - 1 else 0)
      (val32_lt s.mem base src j)).symm
  · intro x hx
    rw [O₅ x (by omega), U₄.mem, U₃.mem, M₂, O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv
