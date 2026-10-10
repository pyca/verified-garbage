import VerifiedGarbage.Proof.Modes.AArch64.Core

/-!
# XORing blocks on AArch64

`xorBlocks_wp`: the loop `xorBlocks` XORs `c ≥ 1` blocks of 16 bytes at
`x14` into those at `x15` (areas that do not overlap), through `x8` and
`x9`, counting down `x17`, and changes nothing else in memory.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (eorR)

/-- `ldr x8, [x14, #d]; ldr x9, [x15, #d]; eor x8, x8, x9; str x8, [x15, #d]`. -/
theorem xorWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x14 + BitVec.ofNat 64 d) 8)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.ldr .x .x8 .x14 d, .ldr .x .x9 .x15 d, eorR .x8 .x8 .x9, .str .x .x8 .x15 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 d)
        (s.mem.readW (s.gpr .x14 + BitVec.ofNat 64 d) 64 ^^^ s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s .x8 .x14 hd hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldr_ok s₁ .x9 .x15 hd
    (by rw [rd₁, wr₁, o₁ _ (by decide)]; exact hr')
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ .x8 .x8 .x9
  have x15₃ : s₃.gpr .x15 = s.gpr .x15 := by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := str_ok s₃ .x8 .x15 hd
    (by rw [wr₃, wr₂, wr₁, x15₃]; exact hw)
  refine ⟨s₄, ?_, ?_, fun r h1 h2 => by rw [g₄, o₃ r h1, o₂ r h2, o₁ r h1], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show ([.ldr .x .x8 .x14 d, .ldr .x .x9 .x15 d, eorR .x8 .x8 .x9, .str .x .x8 .x15 d] : List Instr) =
      [.ldr .x .x8 .x14 d] ++ ([.ldr .x .x9 .x15 d] ++ ([eorR .x8 .x8 .x9] ++ [.str .x .x8 .x15 d])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [m₄, x15₃, v₃, v₂, o₂ _ (by decide), v₁, m₃, m₂, m₁, o₁ _ (by decide)]

/-- XORing, after `j` of `c` blocks. -/
structure XorInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = A + BitVec.ofNat 64 (16 * j)
  x15 : s.gpr .x15 = B + BitVec.ofNat 64 (16 * j)
  x17 : s.gpr .x17 = BitVec.ofNat 64 (c - j)
  xored : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) =
    s₀.mem (A + BitVec.ofNat 64 t) ^^^ s₀.mem (B + BitVec.ofNat 64 t)
  rest : ∀ t, 16 * j ≤ t → t < 16 * c → s.mem (B + BitVec.ofNat 64 t) = s₀.mem (B + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  · intro h; rw [h]; rfl

theorem xorBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c < 2 ^ 59)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : XorInv A B c s₀ 0 s₀) :
    WP isa Core.xorBlocks s₀ (XorInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ XorInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega)
  have hA1 := hA (2 * j + 1) (by omega)
  have hB0 := hB (2 * j) (by omega)
  have hB1 := hB (2 * j + 1) (by omega)
  have hn : 16 * c < 2 ^ 64 := by omega
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have rB : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ e, e < 2 * c →
      InRegions (st.rd ++ st.wr) (B + BitVec.ofNat 64 (8 * e)) 8 := fun st h1 h2 e he => by
    rw [h1, h2]; exact (let ⟨r, hr, hc⟩ := hB e he; ⟨r, List.mem_append_right _ hr, hc⟩)
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := xorWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.x14, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hA0)
    (by rw [hi.x15, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact rB s hi.rd hi.wr _ (by omega))
    (by rw [hi.wr, hi.x15, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := xorWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide) (by decide), hi.x14, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hA1)
    (by rw [g₁ _ (by decide) (by decide), hi.x15, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]
        exact rB s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr) _ (by omega))
    (by rw [wr₁, hi.wr, g₁ _ (by decide) (by decide), hi.x15, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]
        exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x14 .x14 (v := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x15 .x15 (v := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .x17 .x17 (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([.ldr .x .x8 .x14 0, .ldr .x .x9 .x15 0, eorR .x8 .x8 .x9, .str .x .x8 .x15 0,
      .ldr .x .x8 .x14 8, .ldr .x .x9 .x15 8, eorR .x8 .x8 .x9, .str .x .x8 .x15 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1] : List Instr) =
      [.ldr .x .x8 .x14 0, .ldr .x .x9 .x15 0, eorR .x8 .x8 .x9, .str .x .x8 .x15 0] ++
      ([.ldr .x .x8 .x14 8, .ldr .x .x9 .x15 8, eorR .x8 .x8 .x9, .str .x .x8 .x15 8] ++
      ([.addImm .x .x14 .x14 16] ++ ([.addImm .x .x15 .x15 16] ++ [.subImm .x .x17 .x17 1]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have r1 : s₁.gpr .x15 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide), hi.x15]
  have a1 : s₁.gpr .x14 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide), hi.x14]
  have hm : s₅.mem = s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64 ^^^ s₁.mem.readW (B + BitVec.ofNat 64 (16 * j + 8)) 64) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64 ^^^ s.mem.readW (B + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.x15, hi.x14, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area, and on `B`'s beyond the first word.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_xor_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega) hn)]
  have hB₁ : ∀ t, 16 * j + 8 ≤ t → t < 16 * c → s₁.mem (B + BitVec.ofNat 64 t) = s.mem (B + BitVec.ofNat 64 t) :=
    fun t h1 h2 => by
      rw [hm₁, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega)) (by omega) (by omega) (by omega))]
  have g₅ : ∀ r, r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₅ r h5, o₄ r h4, o₃ r h3, g₂ r h1 h2, g₁ r h1 h2]
  have x17₅ : s₅.gpr .x17 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x17,
      VG.Offset.ofNat_sub_ofNat (by omega), show c - j - 1 = c - (j + 1) by omega]
  have hinv : XorInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, x17₅, fun t ht => ?_, fun t h1 h2 => ?_, hi.frame.trans fun x hx => ?_,
      fun r h1 h2 h3 h4 h5 => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide) (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide) (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm, writeW_xor_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega)]; omega), off_sub_toNat B h8 (by omega), addr_add,
          addr_add, show 16 * j + 8 + (t - (16 * j + 8)) = t by omega, hA₁ t (by omega), hB₁ t h8 (by omega),
          hAs t (by omega), hi.rest t (by omega) (by omega)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega)), hm₁,
          writeW_xor_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega)]; omega), off_sub_toNat B h0 (by omega), addr_add,
            addr_add, show 16 * j + (t - 16 * j) = t by omega, hAs t (by omega), hi.rest t h0 (by omega)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega))]
          exact hi.xored t (by omega)
    · rw [hm, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega)) (by omega) (by omega) (by omega)),
        hB₁ t (by omega) h2, hi.rest t (by omega) h2]
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))
      rw [hm, writeW_xor_apply, ite_eq_right (hout _ (by omega)), hm₁, writeW_xor_apply,
        ite_eq_right (hout _ (by omega))]
    · rw [g₅ r h1 h2 h3 h4 h5, hi.regs r h1 h2 h3 h4 h5]
  have hz : isa.eval (.nonzero .x .x17) s₅ = some !(decide (c - (j + 1) = 0)) := by
    rw [eval_nonzero, x17₅, ofNat_beq_zero (by omega)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨by rw [hz, decide_eq_true (by omega)]; rfl, by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by rw [hz, decide_eq_false (by omega)]; rfl, c - (j + 1), by omega, j + 1, rfl, by omega, hinv⟩

end VG.Proof.Modes.AArch64
