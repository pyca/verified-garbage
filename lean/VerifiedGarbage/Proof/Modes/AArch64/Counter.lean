import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.AesCtr.Inc

/-!
# CTR on AArch64: the counter blocks

The running counter block `V` (a number below `2¹²⁸`) is kept as two 64-bit
integers, `hiOf V` and `loOf V`, in `x6` and `x7`. `addc_ok`: `adds`, `adc`
step it by a number below `2⁶⁴`. `ctrBlocks_ok`: the group's `G` counter
blocks, `V … V + G - 1` as 16 big-endian bytes each, to the core's buffer,
and `V + G` to the running counter's slots.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

/-- The high and low halves of the counter block `V`. -/
def hiOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 (V / 2 ^ 64)
def loOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 V

theorem addc_vals (V N : Nat) (hN : N < 2 ^ 64) :
    loOf V + BitVec.ofNat 64 N + BitVec.ofNat 64 (false.toNat) = loOf (V + N) ∧
    hiOf V + BitVec.ofNat 64 (decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat + false.toNat)).toNat =
      hiOf (V + N) := by
  refine ⟨by rw [Bool.toNat_false, BitVec.add_zero, loOf, loOf, BitVec.ofNat_add], ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [hiOf, loOf, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt hN]
  by_cases h : 2 ^ 64 ≤ V % 2 ^ 64 + N
  · rw [decide_eq_true h]
    simp only [Bool.toNat_true]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 + 1 := by omega
    rw [this]; omega
  · rw [decide_eq_false h]
    simp only [Bool.toNat_false]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 := by omega
    rw [this]; omega

/-- `adds x7, x7, nr; adc x6, x6, x10`: the running counter stepped by `nr`
(`x10` zero). -/
theorem addc_ok (s : State) (nr : Reg) {V N : Nat} (hN : N < 2 ^ 64) (hh : s.gpr .x6 = hiOf V)
    (hl : s.gpr .x7 = loOf V) (hn : s.gpr nr = BitVec.ofNat 64 N) (hz : s.gpr .x10 = 0) :
    ∃ s', runBlock isa [.adds .x .x7 .x7 nr, .adc .x .x6 .x6 .x10] s = some s' ∧
      s'.gpr .x6 = hiOf (V + N) ∧ s'.gpr .x7 = loOf (V + N) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨i1, i2⟩ := addc_vals V N hN
  let s₁ := s.addWithCarry .x .x7 (s.read .x .x7) (s.read .x nr) false
  let s₂ := s₁.write .x .x6 (s₁.read .x .x6 + s₁.read .x .x10 + BitVec.ofNat 64 s₁.c.toNat)
  have g₁ : ∀ x, x ≠ .x7 → s₁.gpr x = s.gpr x := fun x hx => by
    simp only [s₁, RegUpd.gpr_addWithCarry, ite_eq_right_iff]; exact fun h => absurd h hx
  have l₁ : s₁.gpr .x7 = loOf (V + N) := by
    simp only [s₁, RegUpd.gpr_addWithCarry, ite_true, BitVec.setWidth_eq, read_x, hl, hn, i1]
  have c₁ : s₁.c = decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat + false.toNat) := by
    simp only [s₁, RegUpd.c_addWithCarry, read_x, hl, hn]
  refine ⟨s₂, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec]
    rfl
  · show (s₁.read .x .x6 + s₁.read .x .x10 + BitVec.ofNat 64 s₁.c.toNat).setWidth 64 = _
    rw [BitVec.setWidth_eq, read_x, read_x, g₁ _ (by decide), g₁ _ (by decide), hh, hz,
      show ∀ x : BitVec 64, x + 0 = x from fun x => by simp, c₁]
    exact i2
  · rw [show s₂.gpr .x7 = s₁.gpr .x7 from RegUpd.gpr_write_of_ne _ _ _ (by decide), l₁]
  · rw [show s₂.gpr x = s₁.gpr x from RegUpd.gpr_write_of_ne _ _ _ h1, g₁ _ h2]

/-- `bytesAt` of the two words written at `P` and `P + 8`: the big-endian
bytes of `V`. -/
theorem bytes_pair (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW P (rev64 (hiOf V))).writeW (P + BitVec.ofNat 64 8) (rev64 (loOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append, bytesAt_writeW_above _ _ _ (by decide) (by decide)
      (by decide),
    show (rev64 (hiOf V)) = AesCtr.rv64 (hiOf V) from rfl, AesCtr.bytesAt_writeW_rv64,
    show (rev64 (loOf V)) = AesCtr.rv64 (loOf V) from rfl, AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

theorem ctrBlock_eq (c : Core) (b : Nat) : c.ctrBlock b =
    ([.rev .x8 .x6] : List Instr) ++ (([stS (c.buf + 2 * b) .x8] : List Instr) ++
      (([.rev .x8 .x7] : List Instr) ++ (([stS (c.buf + 2 * b + 1) .x8] : List Instr) ++
      ([.adds .x .x7 .x7 .x9, .adc .x .x6 .x6 .x10] : List Instr)))) := rfl

variable {c : Core}

/-- Counter block `b` to the buffer, and the running counter stepped. -/
theorem ctrBlock_ok (hL : Layout c) (s : State) {B : Addr} {V b : Nat} (hb : b < c.G) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr) (hh : s.gpr .x6 = hiOf V) (hl : s.gpr .x7 = loOf V)
    (h9 : s.gpr .x9 = 1) (h10 : s.gpr .x10 = 0) :
    ∃ s', runBlock isa (c.ctrBlock b) s = some s' ∧
      s'.gpr .x6 = hiOf (V + 1) ∧ s'.gpr .x7 = loOf (V + 1) ∧
      bytesAt s'.mem (bufAddr c B b) 16 = Spec.Ctr.ofNat V 16 ∧
      Frame [⟨bufAddr c B b, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have h0 : c.buf + 2 * b < c.total := by omega
  have h1 : c.buf + 2 * b + 1 < c.total := by omega
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := rev_ok s .x8 .x6
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_ok (s := s₁) (b := B) (k := c.buf + 2 * b) .x8
    (by rw [o₁ _ (by decide), hB]) (by omega) (by rw [wr₁]; exact slot_wr hw hN h0)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := rev_ok s₂ .x8 .x7
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_ok (s := s₃) (b := B) (k := c.buf + 2 * b + 1) .x8
    (by rw [o₃ _ (by decide), g₂, o₁ _ (by decide), hB]) (by omega)
    (by rw [wr₃, wr₂, wr₁]; exact slot_wr hw hN h1)
  have g₄' : ∀ r, r ≠ .x8 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [g₄, o₃ r hr, g₂, o₁ r hr]
  obtain ⟨s₅, e₅, h₅, l₅, o₅, m₅, rd₅, wr₅⟩ := addc_ok s₄ .x9 (V := V) (N := 1) (by decide)
    (by rw [g₄' _ (by decide), hh]) (by rw [g₄' _ (by decide), hl]) (by rw [g₄' _ (by decide), h9]; rfl)
    (by rw [g₄' _ (by decide), h10])
  have hP : wordAddr B (c.buf + 2 * b) = bufAddr c B b := by
    simp only [wordAddr, bufAddr]; congr 2; omega
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega
  have hmem : s₅.mem = (s.mem.writeW (wordAddr B (c.buf + 2 * b)) (rev64 (hiOf V))).writeW
      (wordAddr B (c.buf + 2 * b + 1)) (rev64 (loOf V)) := by
    rw [m₅, m₄, m₃, m₂, m₁, r₃, g₂, r₁, hh, o₁ .x7 (by decide), hl]
  rw [hP, hP1] at hmem
  refine ⟨s₅, ?_, h₅, l₅, by rw [hmem]; exact bytes_pair _ _ _, ?_, fun r h1 h2 h3 => by rw [o₅ r h1 h2, g₄' r h3],
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctrBlock_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅]
  · rw [hmem]
    have hm : (⟨bufAddr c B b, 16⟩ : Region) ∈ [(⟨bufAddr c B b, 16⟩ : Region)] := List.mem_singleton_self _
    have c0 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have c8 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b + BitVec.ofNat 64 8) (64 / 8) := by
      simp only [Region.Contains, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide
    exact ((Frame.refl _ _).writeW hm _ c0).writeW hm _ c8

/-- The buffer's first `k` blocks. -/
abbrev bufPrefix (c : Core) (B : Addr) (k : Nat) : Region := ⟨B + BitVec.ofNat 64 (8 * c.buf), 16 * k⟩

/-- The first `k` counter blocks to the buffer. -/
theorem ctrLoop_ok (hL : Layout c) {B : Addr} : ∀ (k : Nat), k ≤ c.G → ∀ (s : State) (V : Nat), s.gpr sb = B →
    (⟨B, 8 * c.total⟩ : Region) ∈ s.wr → s.gpr .x6 = hiOf V → s.gpr .x7 = loOf V → s.gpr .x9 = 1 →
    s.gpr .x10 = 0 →
    ∃ s', runBlock isa ((List.range k).flatMap c.ctrBlock) s = some s' ∧
      s'.gpr .x6 = hiOf (V + k) ∧ s'.gpr .x7 = loOf (V + k) ∧
      (∀ j < k, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      Frame [bufPrefix c B k] s.mem s'.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, V, _, _, hh, hl, _, _ =>
    ⟨s, rfl, hh, hl, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl, h9, h10 => by
    have hs := hL.small
    have hroom := hL.room
    have hbuf := hL.buf_le
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctrLoop_ok hL k (by omega) s V hB hw hh hl h9 h10
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctrBlock_ok hL s₁ (V := V + k) (b := k) (by omega)
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
      (by rw [o₁ _ (by decide) (by decide) (by decide), h9]) (by rw [o₁ _ (by decide) (by decide) (by decide), h10])
    refine ⟨s₂, ?_, by rw [h₂, Nat.add_assoc], by rw [l₂, Nat.add_assoc], fun j hj => ?_, ?_,
      fun r h1 h2 h3 => by rw [o₂ r h1 h2 h3, o₁ r h1 h2 h3], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · by_cases hjk : j = k
      · subst hjk; exact b₂
      · rw [bytesAt_frame f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint B (by omega) (by omega) (by omega)) (by decide)]
        exact b₁ j (by omega)
    · refine (f₁.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩).trans
        (f₂.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega) (by omega)

/-- The running counter's slots. -/
abbrev ctrRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.hiSlot), 16⟩

theorem ctrBlocks_eq (c : Core) : c.ctrBlocks =
    ([ldS .x6 c.hiSlot] : List Instr) ++ (([ldS .x7 c.loSlot] : List Instr) ++
      (([.movz .x .x9 (BitVec.ofNat 16 1) 0] : List Instr) ++ (([.movz .x .x10 (BitVec.ofNat 16 0) 0] : List Instr) ++
      ((List.range c.G).flatMap c.ctrBlock ++
      (([stS c.hiSlot .x6] : List Instr) ++ ([stS c.loSlot .x7] : List Instr)))))) := rfl

/-- The group's `G` counter blocks `V … V + G - 1` to the buffer, and the
running counter stepped to `V + G`. -/
theorem ctrBlocks_ok (hL : Layout c) (s : State) {B : Addr} {V : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr)
    (hh : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf V) (hl : s.mem.readW (wordAddr B c.loSlot) 64 = loOf V) :
    ∃ s', runBlock isa c.ctrBlocks s = some s' ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (V + c.G) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (V + c.G) ∧
      Frame [bufRegion c B, ctrRegion c B] s.mem s'.mem ∧
      (∀ r, r ∉ ownRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega
  have own : ∀ r, r ∉ ownRegs → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 := fun r hr => by
    simp only [ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1⟩
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (s := s) (b := B) (k := c.hiSlot) .x6 hB (by omega)
    (inRd (slot_wr hw hN hH))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (s := s₁) (b := B) (k := c.loSlot) .x7
    (by rw [o₁ _ (by decide), hB]) (by omega) (by rw [rd₁, wr₁]; exact inRd (slot_wr hw hN hLo))
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movz_ok s₂ .x9 (v := 1) (by decide)
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := movz_ok s₃ .x10 (v := 0) (by decide)
  have g₄ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₄ r h4, o₃ r h3, o₂ r h2, o₁ r h1]
  obtain ⟨s₅, e₅, h₅, l₅, b₅, f₅, o₅, rd₅, wr₅⟩ := ctrLoop_ok hL (B := B) c.G (Nat.le_refl _) s₄ V
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), hB]) (by rw [wr₄, wr₃, wr₂, wr₁]; exact hw)
    (by rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), v₁, hh])
    (by rw [o₄ _ (by decide), o₃ _ (by decide), v₂, m₁, hl]) (by rw [o₄ _ (by decide), v₃]; rfl) (by rw [v₄]; rfl)
  have hB₅ : s₅.gpr sb = B := by
    rw [o₅ _ (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), hB]
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stS_ok (s := s₅) (b := B) (k := c.hiSlot) .x6 hB₅ (by omega)
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hN hH)
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.loSlot) .x7 (by rw [g₆]; exact hB₅)
    (by omega) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hN hLo)
  have hmem : s₇.mem = (s₅.mem.writeW (wordAddr B c.hiSlot) (hiOf (V + c.G))).writeW (wordAddr B c.loSlot)
      (loOf (V + c.G)) := by
    rw [m₇, m₆, g₆, h₅, l₅]
  have fC : Frame [ctrRegion c B] s₅.mem s₇.mem := by
    rw [hmem]
    have hm : ctrRegion c B ∈ [ctrRegion c B] := List.mem_singleton_self _
    have hc := fun (x : Nat) (hx : x = c.hiSlot ∨ x = c.loSlot) =>
      (VG.Offset.contains B (d := 8 * x) (n := 64 / 8) (e := 8 * c.hiSlot) (k := 16)
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega)
        (by simp only [Core.hiSlot] at hx ⊢; omega))
    exact ((Frame.refl _ _).writeW hm _ (hc _ (.inl rfl))).writeW hm _ (hc _ (.inr rfl))
  refine ⟨s₇, ?_, fun j hj => ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctrBlocks_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, e₇]
  · rw [bytesAt_frame fC (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega)
        (by simp only [Core.hiSlot]; omega)) (by decide)]
    exact b₅ j hj
  · rw [hmem, readW_slot_write _ (by simp only [Core.hiSlot]; omega) (by simp only [Core.loSlot]; omega),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₅' : Frame [bufRegion c B] s.mem s₅.mem := by rw [← m₁, ← m₂, ← m₃, ← m₄]; exact f₅
    exact (f₅'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · obtain ⟨h6, h7, h8, h9, h10⟩ := own r hr
    rw [g₇, g₆, o₅ r h6 h7 h8, g₄ r h6 h7 h9 h10]

end VG.Proof.Modes.AArch64
