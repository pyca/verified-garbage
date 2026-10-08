import VerifiedGarbage.Proof.Camellia.AArch64.Keys

/-!
# Copying blocks on AArch64

As on x86-64: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `x14` to `x15` (areas that do not overlap), through `t0`,
counting down `x17`, and changes nothing else in memory.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (t0)

/-- A byte of a little-endian word stored from a load. -/
theorem writeW_readW_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 64) x =
      if (x - a).toNat < 8 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 8) h
  · rfl

/-- `ldr t0, [x14, #d]; str t0, [x15, #d]`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x14 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.ldr .x t0 .x14 d, .str .x t0 .x15 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .x14 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .x14 + BitVec.ofNat 64 d) 64
  let s₁ := s.write .x t0 v
  have h15 : s₁.gpr .x15 = s.gpr .x15 := RegUpd.gpr_write_of_ne _ _ _ (by decide)
  have ht : s₁.gpr t0 = v := (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .x15 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl⟩
  · have e1 : runBlock isa [.ldr .x t0 .x14 d] s = some s₁ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x hd hr]; rfl
    have e2 : runBlock isa [.str .x t0 .x15 d] s₁ =
        some { s₁ with mem := s₁.mem.writeW (s₁.gpr .x15 + BitVec.ofNat 64 d) (s₁.gpr t0) } := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x hd (by rw [h15]; exact hw)]
    rw [show ([.ldr .x t0 .x14 d, .str .x t0 .x15 d] : List Instr) =
      [.ldr .x t0 .x14 d] ++ [.str .x t0 .x15 d] from rfl, runBlock_append', e1, Option.bind_some, e2]
  · show s.mem.writeW (s₁.gpr .x15 + BitVec.ofNat 64 d) (s₁.gpr t0) = _
    rw [h15, ht]

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [VG.Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [VG.Offset.add_sub_add_left]; exact VG.Offset.not_lt_sub_ofNat h ht hn he

/-- A byte of `A`'s area is not among the 8 at `B + e`. -/
theorem not_in_of_disjoint {A B : Addr} {n t e : Nat} (hsep : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) (ht : t < n)
    (he : e + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ (A + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < 8 :=
  fun h => hsep (A + BitVec.ofNat 64 t) (VG.Offset.contains_base A (by omega) (by omega))
    (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .x14 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .x15 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .x17 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega)
  have hA1 := hA (2 * j + 1) (by omega)
  have hB0 := hB (2 * j) (by omega)
  have hB1 := hB (2 * j + 1) (by omega)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .x14 .x14 (imm := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .x15 .x15 (imm := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .x17 .x17 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.ldr .x t0 .x14 0, .str .x t0 .x15 0, .ldr .x t0 .x14 8, .str .x t0 .x15 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1] : List Instr) =
      [.ldr .x t0 .x14 0, .str .x t0 .x15 0] ++ ([.ldr .x t0 .x14 8, .str .x t0 .x15 8] ++
      ([.addImm .x .x14 .x14 16] ++ ([.addImm .x .x15 .x15 16] ++ [.subImm .x .x17 .x17 1]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega
  have r1 : s₁.gpr .x15 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.dst]
  have a1 : s₁.gpr .x14 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.src]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega) hn)]
  have hc₅ : s₅.gpr .x17 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega), show c - j - 1 = c - (j + 1) by omega]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega)]; omega), off_sub_toNat B h8 (by omega), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega, hA₁ t (by omega), hAs t (by omega)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega)]; omega), off_sub_toNat B h0 (by omega), addr_add,
            show 16 * j + (t - 16 * j) = t by omega, hAs t (by omega)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega))]
          exact hi.copied t (by omega)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : (s₅.gpr .x17 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .x17).trans (by rw [hz]; simp; omega),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .x17).trans (by rw [hz]; simp; omega), c - (j + 1), by omega, j + 1, rfl,
      by omega, hinv⟩

end VG.Proof.Camellia.AArch64
