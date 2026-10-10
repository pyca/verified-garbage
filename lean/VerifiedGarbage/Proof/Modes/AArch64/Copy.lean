import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Impl.Modes.AArch64.Cbc

/-!
# Copying blocks on AArch64

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks of 16 bytes at
`x15` to `x14` (areas that do not overlap), through `x8`, counting down
`x17`, and changes nothing else in memory.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64

/-- `ldr x8, [x15, #d]; str x8, [x14, #d]`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .x14 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.ldr .x .x8 .x15 d, .str .x .x8 .x14 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x14 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s .x8 .x15 hd hr
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := str_ok s₁ .x8 .x14 hd (by rw [wr₁, o₁ _ (by decide)]; exact hw)
  refine ⟨s₂, ?_, by rw [m₂, v₁, o₁ _ (by decide), m₁], fun r hr => by rw [g₂, o₁ r hr], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [show ([.ldr .x .x8 .x15 d, .str .x .x8 .x14 d] : List Instr) = [.ldr .x .x8 .x15 d] ++ [.str .x .x8 .x14 d]
    from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- Copying, after `j` of `c` blocks from `S` to `T`. -/
structure CopyInv (S T : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = T + BitVec.ofNat 64 (16 * j)
  x15 : s.gpr .x15 = S + BitVec.ofNat 64 (16 * j)
  x17 : s.gpr .x17 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (T + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)
  frame : Frame [⟨T, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x8 → r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {S T : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c < 2 ^ 59)
    (hS : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < 2 * c, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 16 * c⟩ ⟨T, 16 * c⟩) (hs : CopyInv S T c s₀ 0 s₀) :
    WP isa Core.copyBlocks s₀ (CopyInv S T c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv S T c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hn : 16 * c < 2 ^ 64 := by omega
  have hSs : ∀ t < 16 * c, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.x15, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hS _ (by omega))
    (by rw [hi.wr, hi.x14, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hT _ (by omega))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.x15, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hS _ (by omega))
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.x14, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]
        exact hT _ (by omega))
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x14 .x14 (v := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x15 .x15 (v := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .x17 .x17 (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([.ldr .x .x8 .x15 0, .str .x .x8 .x14 0, .ldr .x .x8 .x15 8, .str .x .x8 .x14 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1] : List Instr) =
      [.ldr .x .x8 .x15 0, .str .x .x8 .x14 0] ++ ([.ldr .x .x8 .x15 8, .str .x .x8 .x14 8] ++
      ([.addImm .x .x14 .x14 16] ++ ([.addImm .x .x15 .x15 16] ++ [.subImm .x .x17 .x17 1]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have r1 : s₁.gpr .x15 = S + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.x15]
  have a1 : s₁.gpr .x14 = T + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.x14]
  have hm : s₅.mem = s₁.mem.writeW (T + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (S + BitVec.ofNat 64 (16 * j + 8)) 64) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (T + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.x15, hi.x14, addr_add, addr_add, Nat.add_zero]
  have hS₁ : ∀ t < 16 * c, s₁.mem (S + BitVec.ofNat 64 t) = s.mem (S + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega) hn)]
  have x17₅ : s₅.gpr .x17 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.x17,
      VG.Offset.ofNat_sub_ofNat (by omega), show c - j - 1 = c - (j + 1) by omega]
  have hinv : CopyInv S T c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, x17₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat T h8 (by omega)]; omega), off_sub_toNat T h8 (by omega), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega, hS₁ t (by omega), hSs t (by omega)]
      · rw [ite_eq_right (off_sub_not T (Or.inl (by omega)) (by omega) (by omega) (by omega)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat T h0 (by omega)]; omega), off_sub_toNat T h0 (by omega), addr_add,
            show 16 * j + (t - 16 * j) = t by omega, hSs t (by omega)]
        · rw [ite_eq_right (off_sub_not T (Or.inl (by omega)) (by omega) (by omega) (by omega))]
          exact hi.copied t (by omega)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (T + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base T he _ (by simp only [Region.Contains]; omega))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega))]
    · rw [o₅ r h4, o₄ r h3, o₃ r h2, g₂ r h1, g₁ r h1, hi.regs r h1 h2 h3 h4]
  have hz : isa.eval (.nonzero .x .x17) s₅ = some !(decide (c - (j + 1) = 0)) := by
    rw [eval_nonzero, x17₅, ofNat_beq_zero (by omega)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨by rw [hz, decide_eq_true (by omega)]; rfl, by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by rw [hz, decide_eq_false (by omega)]; rfl, c - (j + 1), by omega, j + 1, rfl, by omega, hinv⟩

end VG.Proof.Modes.AArch64
