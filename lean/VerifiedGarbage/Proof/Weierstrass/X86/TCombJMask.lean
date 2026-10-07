import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.Words32

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- `f 0 ||| … ||| f (m - 1)`. -/
def orAll (f : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => 0
  | m + 1 => orAll f m ||| f m

theorem orAll_eq_zero (f : Nat → BitVec 32) : ∀ m, orAll f m = 0 ↔ ∀ i < m, f i = 0
  | 0 => by simp [orAll]
  | m + 1 => by
    rw [orAll]
    have ih := orAll_eq_zero f m
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h
      have h1 := ih.mp h1
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · exact h1 i h
      · obtain rfl : i = m := by omega
        exact h2
    · intro h
      exact BitVec.or_eq_zero_iff.mpr ⟨ih.mpr fun i hi => h i (by omega), h m (by omega)⟩

/-- `eax |= [z + 4 (i + 1)]` for `i < m`, from `eax = [z]`. -/
theorem orChain_ok {base : Addr} {size z : Nat} : ∀ m, ∀ (s : State), Scr s base size → z + 4 * (m + 1) ≤ size →
    s.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) 1 →
    WP isa (.block ((List.range m).map fun i => .alu .or .eax (.mem (sc (z + 4 * (i + 1)))))) s fun t =>
      t.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (m + 1) ∧ CKeeps [.eax] s t
  | 0, s, _, _, hr => WP.block_nil ⟨hr, fun _ _ => rfl, rfl, rfl, rfl⟩
  | m + 1, s, hs, hz, hr => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (orChain_ok m s hs (by omega) hr) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁.keeps (by decide)
    apply WP.of_runBlock
    simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      Option.bind_some, readSrc_sc hs₁ (d := z + 4 * (m + 1)) (by omega), RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', e₁, k₁.2.1]
    refine ⟨rfl, fun r hr' => ?_, k₁.2.1, k₁.2.2.1, k₁.2.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]
    exact k₁.1 r (by simp [hr'])

/-- `ecx` all ones if the `2 n` 32-bit words at `z` are not all zero (`n ≥ 1`), through
`eax`. -/
theorem nzMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n z : Nat} (hn1 : 1 ≤ n)
    (hz : z + 8 * n ≤ size) :
    WP isa (.block (nzMask n z)) s fun t =>
      t.gpr .ecx = bmask (decide (wordsVal s.mem base z n ≠ 0)) ∧ CKeeps [.eax, .ecx] s t := by
  have hnw := hs.nowrap
  rw [nzMask, WP.block_append_iff]
  refine WP.mono (show WP isa (.block (.mov .eax (.mem (sc z)) :: (List.range (2 * n - 1)).map
      fun i => .alu .or .eax (.mem (sc (z + 4 * (i + 1)))))) s (fun s₂ =>
      s₂.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) ∧ CKeeps [.eax] s s₂) by
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .eax (.mem (sc z))]) s (fun s₁ =>
        s₁.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) 1 ∧ CKeeps [.eax] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.map_some,
        readSrc_sc hs (d := z) (by omega), RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [orAll], fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁.keeps (by decide)
    refine WP.mono (orChain_ok (2 * n - 1) s₁ hs₁ (by omega) (by rw [k₁.2.1]; exact e₁)) fun s₂ ⟨e₂, k₂⟩ => ?_
    rw [k₁.2.1, show 2 * n - 1 + 1 = 2 * n by omega] at e₂
    exact ⟨e₂, k₁.trans k₂⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hz' : (orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) = 0) ↔ wordsVal s.mem base z n = 0 := by
    rw [orAll_eq_zero, wordsVal_eq_val32, val32_eq_zero_iff]
    exact forall_congr' fun i => forall_congr' fun _ =>
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left', e₂,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · by_cases h0 : wordsVal s.mem base z n = 0
    · have h1 := hz'.mpr h0
      rw [h1]; simp [h0]; rfl
    · have h1 : orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) ≠ 0 := fun h => h0 (hz'.mp h)
      have : 0 < (orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n)).toNat := by
        refine Nat.pos_of_ne_zero fun h => h1 (BitVec.eq_of_toNat_eq h)
      simp [h0, this]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    exact k₂.1 r (by simp [hr.1])
  · exact k₂.2.1
  · exact k₂.2.2.1
  · exact k₂.2.2.2

end VG.Proof.Weierstrass.X86
