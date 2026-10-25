module

public import VerifiedGarbage.Proof.Modes.AArch64.Counter
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Counter mode with `inc₃₂` on AArch64: the counter blocks

As CTR's (`Counter.lean`), the running counter block `V` is kept as
`hiOf V` and `loOf V` in `x6` and `x7`. `inc32By_ok`: `inc32By t k` steps
it by `j` increments of `inc₃₂` (`ctr32Val V j`, `j` the low 32 bits of
`k`), changing only `x7` (and its temporary `t`). `ctr32Blocks_ok`: the
group's `G` counter blocks, `ctr32Val V 0 … ctr32Val V (G - 1)` as 16
big-endian bytes each, to the core's buffer, and `ctr32Val V G` to the
running counter's slots.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

/-- `inc32By t k`, for a register `k` whose low 32 bits are `j` (modulo
2³²): `x7` from `loOf V` to `loOf (ctr32Val V j)`. -/
theorem inc32By_ok (s : State) {T : Reg} (hT : T ≠ .x7) (k : Reg) {V j : Nat}
    (hk : (s.gpr k).setWidth 32 = BitVec.ofNat 32 j) (hl : s.gpr .x7 = loOf V) :
    ∃ s', runBlock isa (Core.inc32By T k) s = some s' ∧ s'.gpr .x7 = loOf (ctr32Val V j) ∧
      (∀ r, r ≠ .x7 → r ≠ T → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .w T (s.read .w .x7 + s.read .w k)
  let s₂ := s₁.write .x .x7 (s₁.read .x .x7 >>> 32)
  let s₃ := s₂.write .x .x7 (s₂.read .x .x7 <<< 32)
  let s₄ := s₃.write .x .x7 (s₃.read .x .x7 + s₃.read .x T)
  have t₃ : s₃.gpr T = ((s.gpr .x7).setWidth 32 + BitVec.ofNat 32 j).setWidth 64 := by
    simp only [s₃, s₂, RegUpd.gpr_write_of_ne _ _ _ hT, s₁, RegUpd.gpr_write_self]
    rw [← hk]; rfl
  have l₃ : s₃.gpr .x7 = (s.gpr .x7 >>> 32) <<< 32 := by
    simp only [s₃, s₂, RegUpd.gpr_write_self, read_x, BitVec.setWidth_eq, s₁,
      RegUpd.gpr_write_of_ne _ _ _ (Ne.symm hT)]
  refine ⟨s₄, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [Core.inc32By, runBlock_cons, runStep_some, exec]
    rfl
  · show (s₃.read .x .x7 + s₃.read .x T).setWidth 64 = _
    rw [BitVec.setWidth_eq, read_x, read_x, l₃, t₃, hl]
    exact (loOf_ctr32Val V j).symm
  · simp only [s₄, s₃, s₂, RegUpd.gpr_write_of_ne _ _ _ h1, s₁, RegUpd.gpr_write_of_ne _ _ _ h2]

theorem ctr32Block_eq (c : Core) (b : Nat) : c.ctr32Block b =
    ([.rev .x8 .x6] : List Instr) ++ (([stS (c.buf + 2 * b) .x8] : List Instr) ++
      (([.rev .x8 .x7] : List Instr) ++ (([stS (c.buf + 2 * b + 1) .x8] : List Instr) ++
      Core.inc32By .x8 .x9))) := rfl

variable {c : Core}

/-- Counter block `b` to the buffer, and the running counter stepped. -/
theorem ctr32Block_ok (hL : Layout c) (s : State) {B : Addr} {V b : Nat} (hb : b < c.G) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr) (hh : s.gpr .x6 = hiOf V) (hl : s.gpr .x7 = loOf V)
    (h9 : s.gpr .x9 = 1) :
    ∃ s', runBlock isa (c.ctr32Block b) s = some s' ∧
      s'.gpr .x6 = hiOf (ctr32Val V 1) ∧ s'.gpr .x7 = loOf (ctr32Val V 1) ∧
      bytesAt s'.mem (bufAddr c B b) 16 = Spec.Ctr.ofNat V 16 ∧
      Frame [⟨bufAddr c B b, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.total < 2 ^ 64 := by omega_arith
  have h0 : c.buf + 2 * b < c.total := by omega_arith
  have h1 : c.buf + 2 * b + 1 < c.total := by omega_arith
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := rev_ok s .x8 .x6
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_ok (s := s₁) (b := B) (k := c.buf + 2 * b) .x8
    (by rw [o₁ _ (by decide), hB]) (by omega_arith) (by rw [wr₁]; exact slot_wr hw hN h0)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := rev_ok s₂ .x8 .x7
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_ok (s := s₃) (b := B) (k := c.buf + 2 * b + 1) .x8
    (by rw [o₃ _ (by decide), g₂, o₁ _ (by decide), hB]) (by omega_arith)
    (by rw [wr₃, wr₂, wr₁]; exact slot_wr hw hN h1)
  have g₄' : ∀ r, r ≠ .x8 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [g₄, o₃ r hr, g₂, o₁ r hr]
  obtain ⟨s₅, e₅, l₅, o₅, m₅, rd₅, wr₅⟩ := inc32By_ok s₄ (T := .x8) (by decide) .x9 (V := V) (j := 1)
    (by rw [g₄' _ (by decide), h9]; rfl) (by rw [g₄' _ (by decide), hl])
  have hP : wordAddr B (c.buf + 2 * b) = bufAddr c B b := by
    simp only [wordAddr, bufAddr]; congr 2; omega_arith
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega_arith
  have hmem : s₅.mem = (s.mem.writeW (wordAddr B (c.buf + 2 * b)) (rev64 (hiOf V))).writeW
      (wordAddr B (c.buf + 2 * b + 1)) (rev64 (loOf V)) := by
    rw [m₅, m₄, m₃, m₂, m₁, r₃, g₂, r₁, hh, o₁ .x7 (by decide), hl]
  rw [hP, hP1] at hmem
  refine ⟨s₅, ?_, ?_, l₅, by rw [hmem]; exact bytes_pair _ _ _, ?_,
    fun r h1 h2 h3 => by rw [o₅ r h2 h3, g₄' r h3],
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctr32Block_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅]
  · rw [o₅ _ (by decide) (by decide), g₄' _ (by decide), hh, hiOf_ctr32Val]
  · rw [hmem]
    have hm : (⟨bufAddr c B b, 16⟩ : Region) ∈ [(⟨bufAddr c B b, 16⟩ : Region)] := List.mem_singleton_self _
    have c0 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have c8 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b + BitVec.ofNat 64 8) (64 / 8) := by
      simp only [Region.Contains, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide
    exact ((Frame.refl _ _).writeW hm _ c0).writeW hm _ c8

/-- The first `k` counter blocks to the buffer. -/
theorem ctr32Loop_ok (hL : Layout c) {B : Addr} : ∀ (k : Nat), k ≤ c.G → ∀ (s : State) (V : Nat), s.gpr sb = B →
    (⟨B, 8 * c.total⟩ : Region) ∈ s.wr → s.gpr .x6 = hiOf V → s.gpr .x7 = loOf V → s.gpr .x9 = 1 →
    ∃ s', runBlock isa ((List.range k).flatMap c.ctr32Block) s = some s' ∧
      s'.gpr .x6 = hiOf (ctr32Val V k) ∧ s'.gpr .x7 = loOf (ctr32Val V k) ∧
      (∀ j < k, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (ctr32Val V j) 16) ∧
      Frame [bufPrefix c B k] s.mem s'.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, V, _, _, hh, hl, _ =>
    ⟨s, rfl, by rw [ctr32Val_zero, hh], by rw [ctr32Val_zero, hl], fun j hj => by omega_arith, Frame.refl _ _,
      fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl, h9 => by
    have hs := hL.small
    have hroom := hL.room
    have hbuf := hL.buf_le
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Loop_ok hL k (by omega_arith) s V hB hw hh hl h9
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctr32Block_ok hL s₁ (V := ctr32Val V k) (b := k) (by omega_arith)
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
      (by rw [o₁ _ (by decide) (by decide) (by decide), h9])
    refine ⟨s₂, ?_, by rw [h₂, ctr32Val_add], by rw [l₂, ctr32Val_add], fun j hj => ?_, ?_,
      fun r h1 h2 h3 => by rw [o₂ r h1 h2 h3, o₁ r h1 h2 h3], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · by_cases hjk : j = k
      · subst hjk; exact b₂
      · rw [bytesAt_frame f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact b₁ j (by omega_arith)
    · refine (f₁.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩).trans
        (f₂.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega_arith) (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega_arith) (by omega_arith)

theorem ctr32Blocks_eq (c : Core) : c.ctr32Blocks =
    ([ldS .x6 c.hiSlot] : List Instr) ++ (([ldS .x7 c.loSlot] : List Instr) ++
      (([.movz .x .x9 (BitVec.ofNat 16 1) 0] : List Instr) ++
      ((List.range c.G).flatMap c.ctr32Block ++
      (([stS c.hiSlot .x6] : List Instr) ++ ([stS c.loSlot .x7] : List Instr))))) := rfl

/-- The group's `G` counter blocks `ctr32Val V 0 … ctr32Val V (G - 1)` to
the buffer, and the running counter stepped to `ctr32Val V G`. -/
theorem ctr32Blocks_ok (hL : Layout c) (s : State) {B : Addr} {V : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr)
    (hh : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf V) (hl : s.mem.readW (wordAddr B c.loSlot) 64 = loOf V) :
    ∃ s', runBlock isa c.ctr32Blocks s = some s' ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (ctr32Val V j) 16) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctr32Val V c.G) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctr32Val V c.G) ∧
      Frame [bufRegion c B, ctrRegion c B] s.mem s'.mem ∧
      (∀ r, r ∉ ownRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.total < 2 ^ 64 := by omega_arith
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega_arith
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega_arith
  have own : ∀ r, r ∉ ownRegs → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := fun r hr => by
    simp only [ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (s := s) (b := B) (k := c.hiSlot) .x6 hB (by omega_arith)
    (inRd (slot_wr hw hN hH))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (s := s₁) (b := B) (k := c.loSlot) .x7
    (by rw [o₁ _ (by decide), hB]) (by omega_arith) (by rw [rd₁, wr₁]; exact inRd (slot_wr hw hN hLo))
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movz_ok s₂ .x9 (v := 1) (by decide)
  have g₃ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₃ r h3, o₂ r h2, o₁ r h1]
  obtain ⟨s₅, e₅, h₅, l₅, b₅, f₅, o₅, rd₅, wr₅⟩ := ctr32Loop_ok hL (B := B) c.G (Nat.le_refl _) s₃ V
    (by rw [g₃ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₃, wr₂, wr₁]; exact hw)
    (by rw [o₃ _ (by decide), o₂ _ (by decide), v₁, hh])
    (by rw [o₃ _ (by decide), v₂, m₁, hl]) (by rw [v₃]; rfl)
  have hB₅ : s₅.gpr sb = B := by
    rw [o₅ _ (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide), hB]
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stS_ok (s := s₅) (b := B) (k := c.hiSlot) .x6 hB₅ (by omega_arith)
    (by rw [wr₅, wr₃, wr₂, wr₁]; exact slot_wr hw hN hH)
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.loSlot) .x7 (by rw [g₆]; exact hB₅)
    (by omega_arith) (by rw [wr₆, wr₅, wr₃, wr₂, wr₁]; exact slot_wr hw hN hLo)
  have hmem : s₇.mem = (s₅.mem.writeW (wordAddr B c.hiSlot) (hiOf (ctr32Val V c.G))).writeW
      (wordAddr B c.loSlot) (loOf (ctr32Val V c.G)) := by
    rw [m₇, m₆, g₆, h₅, l₅]
  have fC : Frame [ctrRegion c B] s₅.mem s₇.mem := by
    rw [hmem]
    have hm : ctrRegion c B ∈ [ctrRegion c B] := List.mem_singleton_self _
    have hc := fun (x : Nat) (hx : x = c.hiSlot ∨ x = c.loSlot) =>
      (VG.Offset.contains B (d := 8 * x) (n := 64 / 8) (e := 8 * c.hiSlot) (k := 16)
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_arith) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_arith)
        (by simp only [Core.hiSlot] at hx ⊢; omega_arith))
    exact ((Frame.refl _ _).writeW hm _ (hc _ (.inl rfl))).writeW hm _ (hc _ (.inr rfl))
  refine ⟨s₇, ?_, fun j hj => ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [rd₇, rd₆, rd₅, rd₃, rd₂, rd₁],
    by rw [wr₇, wr₆, wr₅, wr₃, wr₂, wr₁]⟩
  · rw [ctr32Blocks_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · rw [bytesAt_frame fC (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_arith) (by omega_arith)
        (by simp only [Core.hiSlot]; omega_arith)) (by decide)]
    exact b₅ j hj
  · rw [hmem, readW_slot_write _ (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₅' : Frame [bufRegion c B] s.mem s₅.mem := by rw [← m₁, ← m₂, ← m₃]; exact f₅
    exact (f₅'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · obtain ⟨h6, h7, h8, h9⟩ := own r hr
    rw [g₇, g₆, o₅ r h6 h7 h8, g₃ r h6 h7 h9]

end VG.Proof.Modes.AArch64
