module

public import VerifiedGarbage.Proof.Mont.X86.CombShiftMath
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Shifting a number's words up by one bit, in a loop over its words

From the lowest word up, each word times 2, plus the one bit carried out
of the word below (in `ecx`).
-/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The `k` words at `o` times 2, modulo their width. -/
theorem shiftOne_ok {s : State} {base : Addr} {size k o : Nat} (hs : Scr s base size)
    (hk : 0 < k) (ho : o + 4 * k ≤ size) :
    WP isa (VG.Impl.Mont.X86.Comb.shiftOne k o) s fun t =>
      Outside base o (4 * k) s.mem t.mem ∧
      val32 t.mem base o k = val32 s.mem base o k * 2 % 2 ^ (32 * k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Mont.X86.Comb.shiftOne
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  refine wordLoop_ok (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outside base o (4 * j) s.mem t.mem ∧
      val32 t.mem base o j = val32 s.mem base o j * 2 % 2 ^ (32 * j) ∧
      (t.gpr .ecx).toNat = val32 s.mem base o j * 2 / 2 ^ (32 * j)) hk
    (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, O, V, C⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm ▸ O, hm ▸ V, by rw [hg _ (by decide) (by decide)]; exact C⟩)
    ⟨u₁.keeps.mono (by decide), u₁.mem ▸ VG.Proof.Mont.Outside.refl _ _ _ _,
      by simp only [val32, Nat.zero_mul, Nat.zero_mod],
      by rw [u₁.gpr]; simp only [val32, Nat.zero_mul, Nat.zero_div]; rfl⟩
    (fun j hj t ⟨K, O, V, C⟩ ej => ?_) (fun u ⟨K, O, V, _⟩ => ⟨O, V, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_at' ht ej (d := o) (by omega)) fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_shr (by decide) fun s₄ u₄ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  have k₉ : Keeps [.eax, .ebx] t s₉ := ((((u₂.keeps.mono (by decide)).widen u₃.keeps).widen
    u₄.keeps).widen u₈.keeps).widen u₉.keeps
  have hs₉ := ht.of_keeps k₉ (by decide)
  have ej₉ : s₉.gpr .ebp = s₉.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [k₉.1 _ (by decide), k₉.1 _ (by decide)]; exact ej
  refine wp_storeS (hs₉.ea_at' ej₉ (d := o) (by omega)) (hs₉.write (d := o + 4 * j) (n := 4) (by omega))
    fun s₁₀ m₁₀ => ?_
  refine wp_movS rfl fun u u₁₁ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (K.trans ((k₉.mono (by decide)).trans (m₁₀.keeps _))).trans (u₁₁.keeps.mono (by decide))
  · have mem₉ : s₉.mem = t.mem := by
      rw [u₉.mem, u₈.mem, u₄.mem, u₃.mem, u₂.mem]
    rw [u₁₁.mem, m₁₀.mem, mem₉]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · have mem₉ : s₉.mem = t.mem := by
      rw [u₉.mem, u₈.mem, u₄.mem, u₃.mem, u₂.mem]
    have word : w32 t.mem base (o + 4 * j) = w32 s.mem base (o + 4 * j) := O.w32 (by omega) (by omega)
    have ecx₈ : s₈.gpr .ecx = t.gpr .ecx := by
      rw [u₈.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    have value : (s₉.gpr .eax).toNat =
        w32 s.mem base (o + 4 * j) * 2 % 2 ^ 32 + val32 s.mem base o j * 2 / 2 ^ (32 * j) := by
      rw [u₉.gpr, BitVec.toNat_add, ecx₈, C, u₈.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, times2_toNat]
      change (w32 t.mem base (o + 4 * j) * 2 % 2 ^ 32 + _) % 2 ^ 32 = _
      rw [word]
      have : val32 s.mem base o j * 2 / 2 ^ (32 * j) < 2 :=
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt s.mem base o j; omega)
      omega
    rw [u₁₁.mem, m₁₀.mem, mem₉, val32_store hn (by omega), V, value, val32_succ, pow32_succ,
      Nat.mul_comm (2 ^ 32), shift_top_one (Nat.two_pow_pos _) (val32_lt _ _ _ _)]
  · rw [u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, shr31_toNat,
      val32_top_bit]
    exact congrArg (· / 2 ^ 31) (O.w32 (by omega) (by omega))
  · rw [u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]
  · rw [u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]

end VG.Proof.Mont.X86.Dynamic
