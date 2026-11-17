module

public import VerifiedGarbage.Proof.Modes.X86_64.Group
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr32
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Modes.X86_64.Counter32`, which only this module used -/

section

/-!
# Counter mode with `inc₃₂` on x86-64: the counter blocks

As CTR's (`Counter.lean`), the running counter block `V` is kept as
`hiOf V` and `loOf V` in `rax` and `rbx`. `inc32By_ok`: `inc32By t` steps it
by `j` increments of `inc₃₂` (`ctr32Val V j`), changing only `rbx` (and
its temporary `t`). `ctr32Blocks_ok`: the group's `G` counter blocks,
`ctr32Val V 0 … ctr32Val V (G - 1)` as 16 big-endian bytes each, to the
core's buffer, and `ctr32Val V G` to the running counter's slots.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

/-- `inc32By k`, for a source `k` that gives `j` (modulo 2³²) in any state
that differs from `s` only in `T`, `rbx` and the flags: `rbx` from
`loOf V` to `loOf (ctr32Val V j)`. -/
theorem inc32By_ok (s : State) {T : Reg} (hT : T ≠ .rbx) (k : Src) {V j : Nat}
    (hk : ∀ t : State, (∀ r, r ≠ T → r ≠ .rbx → t.gpr r = s.gpr r) → t.mem = s.mem →
      readSrc32 t k = some (BitVec.ofNat 32 j))
    (hl : s.gpr .rbx = loOf V) :
    ∃ s', runBlock isa (Core.inc32By T k) s = some s' ∧ s'.gpr .rbx = loOf (ctr32Val V j) ∧
      (∀ r, r ≠ .rbx → r ≠ T → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let lo := (s.gpr .rbx).setWidth 32
  let s₁ := s.setReg32 T lo
  have g₁ : ∀ r, r ≠ T → r ≠ .rbx → s₁.gpr r = s.gpr r := fun r h _ => by
    simp only [s₁, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ h]
  have k₁ : readSrc32 (s.setReg32 T lo) k = some (BitVec.ofNat 32 j) := hk s₁ g₁ rfl
  let a := (s₁.gpr T).setWidth 32
  let r := a + BitVec.ofNat 32 j
  let s₂ := (arithFlags s₁ r (decide (2 ^ 32 ≤ a.toNat + (BitVec.ofNat 32 j).toNat))
    (addOverflow a (BitVec.ofNat 32 j) r)).setReg32 T r
  let x₃ := s₂.gpr .rbx >>> 32
  let s₃ := (s₂.setFlags (some ((s₂.gpr .rbx).getLsbD (32 - 1))) none (some (x₃ == 0)) (some x₃.msb)).setReg .rbx x₃
  let x₄ := s₃.gpr .rbx <<< 32
  let s₄ := (s₃.setFlags (some ((s₃.gpr .rbx).getLsbD (64 - 32))) none (some (x₄ == 0)) (some x₄.msb)).setReg .rbx x₄
  let y := s₄.gpr .rbx + s₄.gpr T
  let s₅ := (arithFlags s₄ y (decide (2 ^ 64 ≤ (s₄.gpr .rbx).toNat + (s₄.gpr T).toNat))
    (addOverflow (s₄.gpr .rbx) (s₄.gpr T) y)).setReg .rbx y
  have rbx₂ : s₂.gpr .rbx = s.gpr .rbx := by
    simp only [s₂, s₁, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hT),
      RegUpd.gpr_arithFlags]
  have rcx₂ : s₂.gpr T = (lo + BitVec.ofNat 32 j).setWidth 64 := by
    simp only [s₂, State.setReg32, RegUpd.gpr_setReg_self, r, a, s₁, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
    simp only [BitVec.setWidth_eq]
  have rcx₄ : s₄.gpr T = s₂.gpr T := by
    simp only [s₄, s₃, RegUpd.gpr_setReg_of_ne _ _ hT, RegUpd.gpr_setFlags]
  have rbx₄ : s₄.gpr .rbx = (s.gpr .rbx >>> 32) <<< 32 := by
    simp only [s₄, x₄, RegUpd.gpr_setReg_self, s₃, x₃, rbx₂]
  refine ⟨s₅, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · have hr : readSrc32 s (.reg .rbx) = some lo := rfl
    simp only [Core.inc32By, runBlock_cons, runStep_some, exec, execAlu32, execShift, hr, Option.map_some,
      Option.bind_some, k₁]
    rfl
  · show y = _
    simp only [y, rbx₄, rcx₄, rcx₂, lo, hl]
    exact (loOf_ctr32Val V j).symm
  · simp only [s₅, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, s₄, s₃, RegUpd.gpr_setFlags, s₂,
      State.setReg32, RegUpd.gpr_setReg_of_ne _ _ h2, s₁]

theorem ctr32Block_eq (c : Core) (b : Nat) : c.ctr32Block b =
    ([movR .rcx .rax] : List Instr) ++ (([.bswap .rcx] : List Instr) ++ (([st (c.buf + 2 * b) .rcx] : List Instr) ++
      (([movR .rcx .rbx] : List Instr) ++ (([.bswap .rcx] : List Instr) ++
      (([st (c.buf + 2 * b + 1) .rcx] : List Instr) ++ Core.inc32By .rcx (.imm 1)))))) := rfl

variable {c : Core}

/-- Counter block `b` to the buffer, and the running counter stepped. -/
theorem ctr32Block_ok (hL : Layout c) (s : State) {B : Addr} {V b : Nat} (hb : b < c.G) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr) (hh : s.gpr .rax = hiOf V) (hl : s.gpr .rbx = loOf V) :
    ∃ s', runBlock isa (c.ctr32Block b) s = some s' ∧
      s'.gpr .rax = hiOf (ctr32Val V 1) ∧ s'.gpr .rbx = loOf (ctr32Val V 1) ∧
      bytesAt s'.mem (bufAddr c B b) 16 = Spec.Ctr.ofNat V 16 ∧
      Frame [⟨bufAddr c B b, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hs]
  have h0 : c.buf + 2 * b < c.ctrSlots := by simp only [Core.ctrSlots]; omega_using [hb, hroom, hbuf]
  have h1 : c.buf + 2 * b + 1 < c.ctrSlots := by simp only [Core.ctrSlots]; omega_using [hb, hroom, hbuf]
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rcx .rax
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ .rcx
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stReg_ok (s := s₂) (b := B) (k := c.buf + 2 * b) .rcx
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hB]) (by rw [wr₂, wr₁]; exact slot_wr hw hN h0)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rcx .rbx
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := bswap_ok s₄ .rcx
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stReg_ok (s := s₅) (b := B) (k := c.buf + 2 * b + 1) .rcx
    (by rw [o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hB])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hN h1)
  have g₆' : ∀ r, r ≠ .rcx → s₆.gpr r = s.gpr r := fun r hr => by
    rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]
  obtain ⟨s₇, e₇, l₇, o₇, m₇, rd₇, wr₇⟩ := inc32By_ok s₆ (T := .rcx) (by decide) (.imm 1) (V := V) (j := 1)
    (fun _ _ _ => rfl) (by rw [g₆' _ (by decide), hl])
  have hP : wordAddr B (c.buf + 2 * b) = bufAddr c B b := by
    simp only [wordAddr, bufAddr]; congr 2; omega_using []
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega_using []
  have hmem : s₇.mem = (s.mem.writeW (wordAddr B (c.buf + 2 * b)) (bswap64 (hiOf V))).writeW
      (wordAddr B (c.buf + 2 * b + 1)) (bswap64 (loOf V)) := by
    rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁, r₅, r₄, g₃, r₂, r₁, hh, o₂ .rbx (by decide), o₁ .rbx (by decide), hl]
  rw [hP, hP1] at hmem
  refine ⟨s₇, ?_, ?_, l₇, by rw [hmem]; exact bytes_pair _ _ _, ?_,
    fun r h1 h2 h3 => by rw [o₇ r h2 h3, g₆' r h3],
    by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctr32Block_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, e₇]
  · rw [o₇ _ (by decide) (by decide), g₆' _ (by decide), hh, hiOf_ctr32Val]
  · rw [hmem]
    have hm : (⟨bufAddr c B b, 16⟩ : Region) ∈ [(⟨bufAddr c B b, 16⟩ : Region)] := List.mem_singleton_self _
    have c0 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have c8 : (⟨bufAddr c B b, 16⟩ : Region).Contains (bufAddr c B b + BitVec.ofNat 64 8) (64 / 8) := by
      simp only [Region.Contains, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide
    exact ((Frame.refl _ _).writeW hm _ c0).writeW hm _ c8

/-- The first `k` counter blocks to the buffer. -/
theorem ctr32Loop_ok (hL : Layout c) {B : Addr} : ∀ (k : Nat), k ≤ c.G → ∀ (s : State) (V : Nat), s.gpr sb = B →
    (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr → s.gpr .rax = hiOf V → s.gpr .rbx = loOf V →
    ∃ s', runBlock isa ((List.range k).flatMap c.ctr32Block) s = some s' ∧
      s'.gpr .rax = hiOf (ctr32Val V k) ∧ s'.gpr .rbx = loOf (ctr32Val V k) ∧
      (∀ j < k, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (ctr32Val V j) 16) ∧
      Frame [bufPrefix c B k] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, V, _, _, hh, hl => ⟨s, rfl, by rw [ctr32Val_zero, hh], by rw [ctr32Val_zero, hl],
      fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl => by
    have hs := hL.small
    have hroom := hL.room
    have hbuf := hL.buf_le
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Loop_ok hL k (by omega_using [hk]) s V hB hw hh hl
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctr32Block_ok hL s₁ (V := ctr32Val V k) (b := k) (by omega_using [hk])
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
    refine ⟨s₂, ?_, by rw [h₂, ctr32Val_add], by rw [l₂, ctr32Val_add], fun j hj => ?_, ?_,
      fun r h1 h2 h3 => by rw [o₂ r h1 h2 h3, o₁ r h1 h2 h3], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · by_cases hjk : j = k
      · subst hjk; exact b₂
      · rw [bytesAt_frame f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint B (by omega_using [hjk]) (by omega_using [hk, hs, hroom, hbuf, hj]) (by omega_using [hk, hs, hroom, hbuf])) (by decide)]
        exact b₁ j (by omega_using [hj, hjk])
    · refine (f₁.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩).trans
        (f₂.sub fun r hr => ⟨bufPrefix c B (k + 1), List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega_using []) (by omega_using [])
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega_using []) (by omega_using [])

/-- The group's `G` counter blocks `ctr32Val V 0 … ctr32Val V (G - 1)` to
the buffer, and the running counter stepped to `ctr32Val V G`. -/
theorem ctr32Blocks_ok (hL : Layout c) (s : State) {B : Addr} {V : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr)
    (hh : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf V) (hl : s.mem.readW (wordAddr B c.loSlot) 64 = loOf V) :
    ∃ s', runBlock isa c.ctr32Blocks s = some s' ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (ctr32Val V j) 16) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctr32Val V c.G) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctr32Val V c.G) ∧
      Frame [bufRegion c B, ctrRegion c B] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hs]
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega_using [hroom]
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega_using [hroom]
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (s := s) (b := B) (k := c.hiSlot) .rax hB
    (inRd (slot_wr hw hN hH))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movS_ok (s := s₁) (b := B) (k := c.loSlot) .rbx
    (by rw [o₁ _ (by decide), hB]) (by rw [rd₁, wr₁]; exact inRd (slot_wr hw hN hLo))
  obtain ⟨s₃, e₃, h₃, l₃, b₃, f₃, o₃, rd₃, wr₃⟩ := ctr32Loop_ok hL (B := B) c.G (Nat.le_refl _) s₂ V
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hB]) (by rw [wr₂, wr₁]; exact hw)
    (by rw [o₂ _ (by decide), v₁, hh]) (by rw [v₂, m₁, hl])
  have hB₃ : s₃.gpr sb = B := by
    rw [o₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (s := s₃) (b := B) (k := c.hiSlot) .rax hB₃
    (by rw [wr₃, wr₂, wr₁]; exact slot_wr hw hN hH)
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := B) (k := c.loSlot) .rbx (by rw [g₄]; exact hB₃)
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hN hLo)
  have hmem : s₅.mem = (s₃.mem.writeW (wordAddr B c.hiSlot) (hiOf (ctr32Val V c.G))).writeW (wordAddr B c.loSlot)
      (loOf (ctr32Val V c.G)) := by
    rw [m₅, m₄, g₄, h₃, l₃]
  have fC : Frame [ctrRegion c B] s₃.mem s₅.mem := by
    rw [hmem]
    have hm : ctrRegion c B ∈ [ctrRegion c B] := List.mem_singleton_self _
    have hc := fun (x : Nat) (hx : x = c.hiSlot ∨ x = c.loSlot) =>
      (VG.Offset.contains B (d := 8 * x) (n := 64 / 8) (e := 8 * c.hiSlot) (k := 16)
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_using [hx]) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_using [hx])
        (by simp only [Core.hiSlot] at hx ⊢; omega_using [hs, hroom]))
    exact ((Frame.refl _ _).writeW hm _ (hc _ (.inl rfl))).writeW hm _ (hc _ (.inr rfl))
  refine ⟨s₅, ?_, fun j hj => ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.ctr32Blocks, runBlock_app, runBlock_app,
      show ([movS .rax c.hiSlot, movS .rbx c.loSlot] : List Instr) = [movS .rax c.hiSlot] ++ [movS .rbx c.loSlot]
        from rfl,
      runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      show ([st c.hiSlot .rax, st c.loSlot .rbx] : List Instr) = [st c.hiSlot .rax] ++ [st c.loSlot .rbx] from rfl,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [bytesAt_frame fC (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_using [hbuf, hj]) (by omega_using [hs, hroom, hbuf, hj])
        (by simp only [Core.hiSlot]; omega_using [hs, hroom])) (by decide)]
    exact b₃ j hj
  · rw [hmem, readW_slot_write _ (by simp only [Core.hiSlot]; omega_using [hs, hroom]) (by simp only [Core.loSlot]; omega_using [hs, hroom]),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_using []), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₃' : Frame [bufRegion c B] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact f₃
    exact (f₃'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · rw [g₅, g₄, o₃ r h1 h2 h3, o₂ r h2, o₁ r h1]

end VG.Proof.Modes.X86_64

end

end

/-! ### `Modes.X86_64.Group32`, which only this module used -/

section

/-!
# One group of blocks of counter mode with `inc₃₂` on x86-64, for any core

`ctr32Group_wp`: `ctrGroup_wp` (`Group.lean`) for `ctr32`'s groups, whose
counter blocks are `inc₃₂`'s (`ctr32Blocks_ok`): block `j` of the data
becomes the XOR with the encryption of `ctr32Val V j` (`ctr32Out`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The data loop of `ctr32`, before group `g`, from the counter block `V`
with the key `k`. -/
structure GInv32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctr32Val V (c.G * g))
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctr32Val V (c.G * g))
  data : DInv 16 s₀.mem s.mem D n (c.G * g) (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop of `ctr32`, done. -/
structure GDone32 (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv 16 s₀.mem s.mem D n n (ctr32Out (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctr32Group_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv32 cs s₀ B D n k V g s) :
    WP isa c.ctr32Group s fun s' => (s'.zf = some true ∧ GDone32 cs s₀ B D n k V s') ∨
      (s'.zf = some false ∧ GInv32 cs s₀ B D n k V (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, dc, dbp, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, lc, lbp, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  obtain hv : v < 2 ^ 64 := by omega_using [hfitD]
  obtain hc0 : 0 < cc := by omega_using [hG0, hk]
  obtain hcG : cc ≤ c.G := by omega_using []
  obtain hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega_using [hc0]
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * c.ctrSlots → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    fun h => VG.Offset.sub_base B h
  obtain subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ := Region.sub_prefix (by simp only [Core.ctrSlots]; omega_using [hroom])
  obtain stkS : ∀ {R : Region}, Region.Sub R ⟨B, 8 * c.ctrSlots⟩ → ∀ r ∈ stkList c (s₀.gpr .rsp),
      Region.Disjoint R r := fun h => hp.stk.disj ⟨_, hp.scr.wr, h⟩
  obtain mSlot : ∀ j, c.slots ≤ j → j < c.ctrSlots → ∀ r ∈ coreFrame c B (s₀.gpr .rsp),
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 =>
    coreFrame_disj (VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hN, h2]))
      (stkS (VG.Offset.sub_base B (by omega_using [h2])))
  obtain inT : ∀ t, t < 2 * c.G → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf, ht]) (by omega_using [hsm, hroom, hbuf, ht])
  obtain inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_using [ht]) (by omega_using [hfitD, ht])
  obtain sepAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right (subS (by simp only [Core.ctrSlots]; omega_using [hroom, hbuf]))
  -- The counter blocks.
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Blocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctr32Group
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide) (by decide), hi.base]
  obtain subBC : ∀ r ∈ [bufRegion c B, ctrRegion c B], Region.Sub r ⟨B, 8 * c.ctrSlots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine subS ?_ <;> simp only [Core.hiSlot, Core.ctrSlots] <;> omega_using [hroom, hbuf]
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr fun _ h => h
    · exact .inl (VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_using [])
        (by simp only [Core.hiSlot]; omega_using [hsm, hroom])).symm) ⟨fun r hr => ⟨_, hwS, subBC r hr⟩, rd₁, wr₁, runBlock_syms e₁⟩ fun r hr => by
    obtain ⟨h1, h2, h3, -⟩ := of_not_modeRegs hr
    exact o₁ r h1 h2 h3
  -- The keystream.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  obtain rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [o₁ _ (by decide) (by decide) (by decide), hi.rsp]
  rw [rsp₁] at f₂
  obtain keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (mSlot j h1 h2) (by decide)
  obtain keep₁ : ∀ j, c.slots ≤ j → j < c.slots + 6 →
      s₁.mem.readW (wordAddr B j) 64 = s.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint B (Or.inr (by omega_using [hbuf, h1])) (by omega_using [hsm, hroom, h2]) (by omega_using [hsm, hroom, hbuf])
      · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_using [h2]) (by omega_using [hsm, hroom, h2])
          (by simp only [Core.hiSlot]; omega_using [hsm, hroom])) (by decide)
  -- The count.
  obtain left₂ : s₂.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₂, o₁ _ la lb lc, hi.leftR]
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, o₁ _ da db dc, hi.dataR]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  refine WP.seq (WP.mono_syms (groupCount_wp (by omega_using [hsm, hroom, hbuf]) lc left₂ hv) fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ sy₃ => ?_)
  obtain base₃ : s₃.gpr sb = B := by rw [o₃ _ (by decide), base₂]
  obtain ⟨s₄, e₄, a₄, b₄, t₄, o₄, m₄, rd₄, wr₄⟩ := xorArgs_ok (by omega_using [hsm, hroom, hbuf]) da s₃ base₃
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  obtain mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  -- The keystream XORed into the group's blocks.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A := T) (B := A) hc0 (by omega_using [hsm, hroom, hbuf])
    (fun t ht => by rw [rd₄', wr₄']; exact inRd (inT t (by omega_using [ht])))
    (fun t ht => by rw [wr₄']; exact inA t ht) sepAT.symm
    ⟨by rw [a₄]; simp [T], by rw [b₄, o₃ _ dc, data₂]; simp [A],
      by rw [o₄ _ (by decide) (by decide) (by decide), c₃, Nat.sub_zero], fun t ht => by omega_using [ht], fun t _ _ => rfl,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₅ h₅ sy₅ => ?_)
  obtain f₅ : Frame [⟨A, 16 * cc⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact h₅.frame
  obtain g₅ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₅.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 => h₅.regs r h1 h2 h3 h4
  obtain keep₄ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₅.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₅ r h1 h2 h3 h4, o₄ r h1 h2 h5, o₃ r h3]
  obtain base₅ : s₅.gpr sb = B := by
    rw [keep₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), base₂]
  obtain left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 v := by rw [keep₄ _ la lb lc lbp l10, left₂]
  obtain r10₅ : s₅.gpr .r10 = BitVec.ofNat 64 cc := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), t₄, c₃]
  have rbx₅ : s₅.gpr .rbx = A + BitVec.ofNat 64 (16 * cc) := h₅.rbx
  obtain rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [keep₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsp₂,
      o₁ _ (by decide) (by decide) (by decide), hi.rsp]
  obtain wr₅' : s₅.wr = s.wr := by rw [h₅.wr, wr₄']
  obtain rd₅' : s₅.rd = s.rd := by rw [h₅.rd, rd₄']
  obtain keep₅ : ∀ j, j < c.ctrSlots → s₅.mem.readW (wordAddr B j) 64 = s₂.mem.readW (wordAddr B j) 64 :=
    fun j hj => f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right
        (subS (by omega_using [hj]))).symm) (by decide)
  -- On to the next group.
  obtain ⟨s₆, e₆, d₆, l₆, z₆, o₆, m₆, rd₆, wr₆⟩ := advance_ok hdl d10 s₅
  obtain hz : s₆.zf = some (decide (v = cc)) := by
    rw [z₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat_beq hv (by omega_using [hfitD])]
  obtain ready₆ : cs.Ready s₆ B k := by
    refine cs.ready_frame ready₂ (by rw [m₆]; exact f₅) (fun r hr => ?_) ⟨fun r hr => ?_, ?_, ?_, ?_⟩ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((hp.sep.sub_left (VG.Offset.sub_base D (by omega_using [hkc]))).sub_right subCore).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [wr₂, wr₁]; exact hwD, VG.Offset.sub_base D (by omega_using [hkc])⟩
    · rw [rd₆, rd₅', rd₂, rd₁]
    · rw [wr₆, wr₅', wr₂, wr₁]
    · rw [runBlock_syms e₆, sy₅, runBlock_syms e₄, sy₃]
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := of_not_modeRegs hr
      rw [o₆ r h6 h7, keep₄ r h1 h2 h3 h4 h5]
  -- The data.
  obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨B, 8 * c.ctrSlots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain dCore : ∀ r ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, 16 * n⟩ r :=
    coreFrame_disj (hp.sep.sub_right subCore) (hp.stk.disj ⟨_, hp.dat, fun _ h => h⟩)
  obtain hn64 : 16 * n ≤ 2 ^ 64 := by omega_using [hfitD]
  obtain via₁₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [f₂.bytes (R := ⟨D, 16 * n⟩) dCore hn64 hin, f₁.bytes (R := ⟨D, 16 * n⟩) (hdS subBC) hn64 hin]
  obtain hdata : DInv 16 s₀.mem s₆.mem D n (c.G * g + cc) (ctr32Out (cs.cipher k) s₀.mem D V) := by
    intro i hin
    rw [m₆]
    by_cases hin1 : 16 * (c.G * g) ≤ i ∧ i < 16 * (c.G * g) + 16 * cc
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * (c.G * g)) := by
        rw [addr_add, show 16 * (c.G * g) + (i - 16 * (c.G * g)) = i by omega_using [hin1]]
      let t := i - 16 * (c.G * g)
      obtain hj : t / 16 < c.G := by omega_using [hin1]
      obtain hu : t % 16 < 16 := Nat.mod_lt _ (by decide)
      obtain eT : T + BitVec.ofNat 64 t = bufAddr c B (t / 16) + BitVec.ofNat 64 (t % 16) := by
        simp only [T, bufAddr]
        rw [addr_add, addr_add, show 8 * c.buf + 16 * (t / 16) + t % 16 = 8 * c.buf + t by omega_using []]
      obtain hks : s₂.mem (T + BitVec.ofNat 64 t) =
          (cs.cipher k (Spec.Ctr.ofNat (ctr32Val (ctr32Val V (c.G * g)) (t / 16)) 16)).getD (t % 16) 0 := by
        rw [eT, ← bytesAt_getD s₂.mem _ hu, ks₂ _ hj, tb₁ _ hj]
      obtain hd₂ : s₂.mem (A + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, via₁₂ i hin, hi.data i hin, ite_eq_right (by omega_using [hin1])]
      rw [e1, h₅.xored _ (by omega_using [hin1]), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [hin1]),
        ctr32Out_getD (cs.cipher_len k) _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega_using [],
        ctr32Val_add, show c.G * g + t / 16 = i / 16 by omega_using [hin1], show t % 16 = i % 16 by omega_using [hin1], BitVec.xor_comm]
    · have hout : ∀ r ∈ [(⟨A, 16 * cc⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_using [hin1]) (by omega_using [hn64, hin]) (by omega_using [hc0]) (by omega_using [hkc, hn64])
      rw [f₅ _ hout, via₁₂ i hin, hi.data i hin]
      by_cases h2 : i < 16 * (c.G * g)
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * (c.G * g + cc) by omega_using [hin1, h2])]
  -- The slots.
  obtain saved₆ : ∀ i < 6, s₆.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [m₆, keep₅ _ (by simp only [Core.ctrSlots]; omega_using [hroom, hi6]), keep₂ _ (by omega_using []) (by simp only [Core.ctrSlots]; omega_using [hroom, hi6]),
      keep₁ _ (by omega_using []) (by omega_using [hi6]), hi.saved i hi6]
  obtain hiSlot₆ : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
      s₆.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
    obtain h1 : c.slots ≤ j := by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using []
    obtain h2 : j < c.ctrSlots := by
      rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot, Core.ctrSlots] <;> omega_using [hroom]
    rw [m₆, keep₅ j h2, keep₂ j h1 h2]
  obtain fr₆ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s.mem s₆.mem := by
    rw [m₆]
    refine ((f₁.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subBC r hr⟩).trans
      (f₂.sub (coreFrame_sub ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, subCore⟩))).trans (f₅.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base D (by omega_using [hkc])⟩
  obtain fr : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₆.mem := hi.frame.trans fr₆
  obtain base₆ : s₆.gpr sb = B := by rw [o₆ _ (Ne.symm dsb) (Ne.symm lsb), base₅]
  obtain rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by rw [o₆ _ (Ne.symm dsp) (Ne.symm lsp), rsp₅]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅', hi.rd]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅', hi.wr]
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], base₆, rsp₆, saved₆, ?_, fr, rd₆', wr₆'⟩
    rw [show n = c.G * g + cc by omega_using [hkc, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₆, rsp₆, ready₆, saved₆, ?_, ?_,
      by rw [Nat.mul_succ]; omega_using [hdone], ?_, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₆', wr₆'⟩
    · rw [d₆, rbx₅, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega_using []]
    · rw [l₆, left₅, r10₅, VG.Offset.ofNat_sub_ofNat (by omega_using []), hcc,
        show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]
    · rw [hiSlot₆ _ (.inl rfl), h₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]
    · rw [hiSlot₆ _ (.inr rfl), l₁, ctr32Val_add, show c.G * g + c.G = c.G * (g + 1) by rw [Nat.mul_succ]]

end VG.Proof.Modes.X86_64

end

end

/-! ### `Modes.X86_64.Setup32`, which only this module used -/

section

/-!
# Counter mode with `inc₃₂` on x86-64: the entry

`setup32_ok`: the entry block of `ctr32` does what `ctr`'s does
(`setup_ok`), but writes `inc₃₂ⁿ(T₁)` back (`ctr32Val V n`) rather than
`T₁ + n`.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

theorem ctr32Setup_eq (c : Core) (r : CtrRegs) : c.ctr32Setup r =
    ([.mov .rax (.mem (at_ r.ctr 0))] : List Instr) ++ (([.bswap .rax] : List Instr) ++
      (([.mov .rbx (.mem (at_ r.ctr 8))] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([st c.hiSlot .rax] : List Instr) ++ (([st c.loSlot .rbx] : List Instr) ++
      (Core.inc32By .rax (.reg r.n) ++ (([movS .rax c.hiSlot] : List Instr) ++
      (([.bswap .rax] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([.store (at_ r.ctr 8) .rbx] : List Instr) ++ ([.store (at_ r.ctr 0) .rax] : List Instr))))))))))) := rfl

variable {c : Core}

/-- The entry block. -/
theorem setup32_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.ctrSlots) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.ctrSlots⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctr32Setup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 6, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .rbx)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctr32Val (ctrVal s.mem P) (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  obtain sl : ∀ k, c.slots ≤ k → k < c.ctrSlots → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  obtain p0 : P + BitVec.ofNat 64 0 = P := by simp
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  obtain b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  have keep₁ : ∀ x, x ≠ sb → s₁.gpr x = s.gpr x := o₁
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₁ b₁'
    (fun i hi => by rw [wr₁]; exact sl _ (by omega_arith) (by simp only [Core.ctrSlots]; omega_arith))
    (by omega_arith)
  let s₄ := s₂
  have m₄e : s₄.mem = s₂.mem := rfl
  have g₄' : s₄.gpr = s₁.gpr := g₂
  obtain wr₄' : s₄.wr = s.wr := by rw [show s₄.wr = s₂.wr from rfl, wr₂, wr₁]
  obtain rd₄' : s₄.rd = s.rd := by rw [show s₄.rd = s₂.rd from rfl, rd₂, rd₁]
  obtain keep₄ : ∀ x, x ≠ sb → s₄.gpr x = s.gpr x := fun x hx => by rw [g₄', keep₁ x hx]
  obtain P₄ : s₄.gpr r.ctr = P := by rw [keep₄ _ hr.ctr.1, hP]
  obtain fe : Frame [modeRegion c B] s.mem s₄.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega_arith) (by omega_arith)⟩
  obtain dP : ∀ k, c.slots ≤ k → k < c.ctrSlots → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega_arith))).symm
  obtain memP : bytesAt s₄.mem P 16 = bytesAt s.mem P 16 :=
    bytesAt_frame fe (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith))) (by decide)
  -- The counter.
  obtain inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega_arith)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  obtain mP : ∀ d, d + 8 ≤ 16 →
      s₄.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega_arith) (by omega_arith)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith))) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ld_ok s₄ .rax r.ctr 0
    (by rw [rd₄', wr₄', P₄]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := bswap_ok s₅ .rax
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := ld_ok s₆ .rbx r.ctr 8
    (by rw [rd₆, wr₆, rd₅, wr₅, rd₄', wr₄', o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := bswap_ok s₇ .rbx
  obtain g₈ : ∀ x, x ≠ .rax → x ≠ .rbx → s₈.gpr x = s₄.gpr x := fun x h1 h2 => by
    rw [o₈ x h2, o₇ x h2, o₆ x h1, o₅ x h1]
  obtain mP0 := mP 0 (by decide)
  rw [p0] at mP0
  obtain rax₈ : s₈.gpr .rax = hiOf V := by
    rw [o₈ _ (by decide), o₇ _ (by decide), r₆, r₅, P₄, p0, mP0, hv]; rfl
  obtain rbx₈ : s₈.gpr .rbx = loOf V := by
    rw [r₈, r₇, m₆, m₅, o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄, mP 8 (by decide), lv]; rfl
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅, rd₄']
  obtain b₈ : s₈.gpr sb = B := by rw [g₈ _ (by decide) (by decide), g₄', b₁']
  obtain hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega_arith
  obtain hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega_arith
  obtain ⟨s₉, e₉, m₉, g₉, rd₉, wr₉⟩ := stReg_ok (s := s₈) (b := B) (k := c.hiSlot) .rax b₈
    (by rw [wr₈']; exact sl _ (by simp only [Core.hiSlot]; omega_arith) hH)
  obtain ⟨s₁₀, e₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := stReg_ok (s := s₉) (b := B) (k := c.loSlot) .rbx (by rw [g₉, b₈])
    (by rw [wr₉, wr₈']; exact sl _ (by simp only [Core.loSlot]; omega_arith) hLo)
  let N := (s.gpr r.n).toNat
  obtain n₁₀ : s₁₀.gpr r.n = BitVec.ofNat 64 N := by
    rw [g₁₀, g₉, g₈ _ hr.n.2.1 hr.n.2.2, keep₄ _ hr.n.1]; simp [N]
  obtain ⟨s₁₁, e₁₁, l₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := inc32By_ok s₁₀ (T := .rax) (by decide) (.reg r.n) (V := V)
    (j := N) (fun t ht _ => by
      simp only [readSrc32, ht _ hr.n.2.1 hr.n.2.2, n₁₀, Option.some.injEq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_arith) (by rw [g₁₀, g₉, rbx₈])
  obtain b₁₁ : s₁₁.gpr sb = B := by rw [o₁₁ _ (by decide) (by decide), g₁₀, g₉, b₈]
  obtain ⟨s₁₁b, e₁₁b, v₁₁b, o₁₁b, m₁₁b, rd₁₁b, wr₁₁b⟩ := movS_ok (s := s₁₁) (b := B) (k := c.hiSlot) .rax b₁₁
    (by rw [rd₁₁, wr₁₁, rd₁₀, wr₁₀, rd₉, wr₉, rd₈', wr₈']; exact inRd (sl _ (by simp only [Core.hiSlot]; omega_arith) hH))
  obtain h₁₁ : s₁₁b.gpr .rax = hiOf (ctr32Val V N) := by
    rw [v₁₁b, m₁₁, m₁₀, readW_slot_write _ (by omega_arith) (by omega_arith),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith), m₉, Mem.readW_writeW_self64, rax₈,
      hiOf_ctr32Val]
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := bswap_ok s₁₁b .rax
  obtain ⟨s₁₃, e₁₃, r₁₃, o₁₃, m₁₃, rd₁₃, wr₁₃⟩ := bswap_ok s₁₂ .rbx
  obtain keep₁₃ : ∀ x, x ≠ .rax → x ≠ .rbx → s₁₃.gpr x = s₈.gpr x := fun x h1 h2 => by
    rw [o₁₃ x h2, o₁₂ x h1, o₁₁b x h1, o₁₁ x h2 h1, g₁₀, g₉]
  obtain P₁₃ : s₁₃.gpr r.ctr = P := by rw [keep₁₃ _ hr.ctr.2.1 hr.ctr.2.2, g₈ _ hr.ctr.2.1 hr.ctr.2.2, P₄]
  obtain wr₁₃' : s₁₃.wr = s.wr := by rw [wr₁₃, wr₁₂, wr₁₁b, wr₁₁, wr₁₀, wr₉, wr₈']
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := stM_ok s₁₃ r.ctr .rbx 8 (by rw [P₁₃, wr₁₃']; exact inP 8 (by decide))
  obtain ⟨s₁₅, e₁₅, m₁₅, g₁₅, rd₁₅, wr₁₅⟩ := stM_ok s₁₄ r.ctr .rax 0
    (by rw [g₁₄, P₁₃, wr₁₄, wr₁₃']; exact inP 0 (by decide))
  obtain mem₁₀ : s₁₀.mem = (s₄.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₁₀, m₉, g₉, rax₈, rbx₈, m₈, m₇, m₆, m₅]
  obtain mem₁₅ : s₁₅.mem = (s₁₀.mem.writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf (ctr32Val V N)))).writeW P
      (bswap64 (hiOf (ctr32Val V N))) := by
    rw [m₁₅, g₁₄, P₁₃, p0, m₁₄, P₁₃, m₁₃, m₁₂, m₁₁b, m₁₁, o₁₃ .rax (by decide), r₁₂, h₁₁, r₁₃, o₁₂ .rbx (by decide),
      o₁₁b .rbx (by decide), l₁₁]
  -- The frames.
  obtain fS : Frame [modeRegion c B] s₄.mem s₁₀.mem := by
    rw [mem₁₀]
    obtain hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega_arith)
      (by simp only [Core.hiSlot]; omega_arith) (by omega_arith))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith) (by omega_arith))
  obtain fP : Frame [⟨P, 16⟩] s₁₀.mem s₁₅.mem := by
    rw [mem₁₅]
    obtain hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  obtain thruP : ∀ k, c.slots ≤ k → k < c.ctrSlots →
      s₁₅.mem.readW (wordAddr B k) 64 = s₁₀.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  obtain b8 : ∀ k, k < c.ctrSlots → 8 * k < 2 ^ 64 := fun k hk => by omega_arith
  obtain mem10 : ∀ k, c.slots ≤ k → k < c.ctrSlots → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₁₀.mem.readW (wordAddr B k) 64 = s₄.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₁₀, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH), ite_eq_right hh]
  obtain hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  refine ⟨s₁₅, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_,
    by rw [rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁b, rd₁₁, rd₁₀, rd₉, rd₈'], by rw [wr₁₅, wr₁₄, wr₁₃']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctr32Setup_eq,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      runBlock_app, e₈, Option.bind_some, runBlock_app, e₉, Option.bind_some, runBlock_app, e₁₀, Option.bind_some,
      runBlock_app, e₁₁, Option.bind_some, runBlock_app, e₁₁b, Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃,
      Option.bind_some, runBlock_app, e₁₄, Option.bind_some, e₁₅]
  · rw [g₁₅, g₁₄, keep₁₃ _ (by decide) (by decide), b₈]
  · have k1 : c.slots ≤ c.slots + i := by omega_arith
    obtain k2 : c.slots + i < c.ctrSlots := by simp only [Core.ctrSlots]; omega_arith
    rw [thruP _ k1 k2, mem10 _ k1 k2 (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith),
      m₄e, v₂ i hi, keep₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega_arith) hH, mem₁₀,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega_arith) hLo, mem₁₀, Mem.readW_writeW_self64]
  · rw [mem₁₅]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · rw [g₁₅, g₁₄, keep₁₃ x h2 h3, g₈ x h2 h3, keep₄ x h1]

end VG.Proof.Modes.X86_64

end

end


/-!
# Counter mode with `inc₃₂` on x86-64, for any core: the whole function

`ctr32_wp`: `c.ctr32 r`, for a core `c` with `CoreSpec c` and its
arguments in the registers `r`, transforms the `n` blocks at `D` by
`Spec.Gcm.ctr32` with the core's cipher under the key `k` that its key
arguments give (on GCM's blocks, `onBlocks`), from the counter block at
`P`, which it replaces with `inc₃₂ⁿ` of it; it keeps the callee-saved
registers, and writes nothing but the scratch buffer, the counter block and
the data. As `ctr_wp` (`Ctr.lean`), whose proof it follows.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem ctr32Loop_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {s : State} (hi : GInv32 cs s₀ B D n k V 0 s) :
    WP isa (.loop c.ctr32Group .ne) s (GDone32 cs s₀ B D n k V) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ GInv32 cs s₀ B D n k V g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (ctr32Group_wp cs hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨by simp [X86_64.eval, z], n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega_arith, g + 1, rfl, d⟩

/-- `CoreSpec.Ready`, `prepare`'s and the test's states, and the loop. -/
theorem ctr32_wp (cs : CoreSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {s₀ : State} {B P D : Addr} {n : Nat}
    {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D)
    (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots) (hwP : (⟨P, 16⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨B, 8 * c.ctrSlots⟩) (sPD : Region.Disjoint ⟨P, 16⟩ ⟨D, 16 * n⟩)
    (fitD : D.toNat + 16 * n ≤ 2 ^ 64) (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] k)
    (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.ctr32 r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      Spec.Gcm.blocksAt s'.mem D n =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.blockAt s₀.mem P) (Spec.Gcm.blocksAt s₀.mem D n) ∧
      Spec.Gcm.blockAt s'.mem P = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt s₀.mem P) ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_using [hsm]
  obtain hNs : c.slots ≤ c.ctrSlots := by simp only [Core.ctrSlots]; omega_using [hroom]
  obtain b8 : ∀ j, j < c.ctrSlots → 8 * j < 2 ^ 64 := fun j hj => by omega_using [hN, hj]
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  -- The entry.
  obtain ⟨s₁a, e₁a, b₁a, sv₁, hi₁, lo₁, bP₁, f₁, g₁a, rd₁a, wr₁a⟩ := setup32_ok hL hr s₀ hB hs hP hwP sPS
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok s₁a r hdn hdl
  obtain g₁ : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → x ≠ c.dataReg → x ≠ c.leftReg → s₁.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [g₁b x h4 h5, g₁a x h1 h2 h3]
  obtain b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), b₁a]
  obtain rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rd₁a]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wr₁a]
  have mem₁ : s₁.mem = s₁a.mem := m₁b
  unfold Core.ctr32
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, e₁a, Option.bind_some, e₁b], ?_⟩)
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_using [hroom])
  obtain f₁' : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁]
    exact f₁.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, List.mem_cons_self, subMode⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  obtain hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.ctrSlots⟩, ⟨P, 16⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₁ x (kr x hx).1 (kr x hx).2.1 (kr x hx).2.2 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₁ wr₁
      (by rw [runBlock_syms e₁b, runBlock_syms e₁a]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, rsp₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  rw [show s₁.gpr .rsp = s₀.gpr .rsp from g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₂
  obtain keep₂ : ∀ j, c.slots ≤ j → j < c.ctrSlots →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (hstk.coreFrame_disj (VG.Offset.disjoint_base B (by omega_using [h1]) (by omega_using [hN, h2]))
      ⟨_, hs.wr, VG.Offset.sub_base B (by omega_using [h2])⟩) (by decide)
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain left₃ : s₃.gpr c.leftReg = s₀.gpr r.n := by rw [g₃, lr₂, lr₁, g₁a _ hr.n.1 hr.n.2.1 hr.n.2.2]
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, ← g₃, left₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₃ : s₃.mem = s₂.mem := m₃
  obtain b₃ : s₃.gpr sb = B := by rw [g₃, b₂]
  obtain rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃, rsp₂, g₁ _ (by decide) (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂']
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂']
  let V := ctrVal s₀.mem P
  obtain hp : GPre c s₃ B D n :=
    ⟨⟨by rw [wr₃']; exact hs.wr, hs.fit⟩, by rw [wr₃']; exact hwD, sDS, fitD, hstk.congr rsp₃ wr₃'⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone32 cs s₃ B D n k V)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₃, rfl, fun _ _ => rfl, fun i hi' => by omega, Frame.refl _ _, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    obtain hsl : ∀ j, j = c.hiSlot ∨ j = c.loSlot →
        s₃.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j hj => by
      rw [mem₃]
      exact keep₂ j (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot] <;> omega_using [])
        (by rcases hj with rfl | rfl <;> simp only [Core.hiSlot, Core.loSlot, Core.ctrSlots] <;> omega_using [hroom])
    refine ctr32Loop_wp cs hp ⟨b₃, rfl, cs.ready_frame ready₂ (by rw [mem₃]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₃, wr₃, runBlock_syms e₃⟩ (fun r _ => by rw [g₃]), fun _ _ => rfl, ?_, ?_, by omega_using [hn0], ?_, ?_,
      fun i _ => by rw [ite_eq_right (by omega_using [])], Frame.refl _ _, rfl, rfl⟩
    · rw [g₃, dr₂, dr₁, g₁a _ hr.data.1 hr.data.2.1 hr.data.2.2, hD]; simp
    · rw [left₃, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
    · rw [hsl _ (.inl rfl), mem₁, hi₁, Nat.mul_zero, ctr32Val_zero]
    · rw [hsl _ (.inr rfl), mem₁, lo₁, Nat.mul_zero, ctr32Val_zero]
  -- The exit.
  obtain hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  obtain hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₄
    d₄.base hsv hinj (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₃', wr₃']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega_using [hroom, hi'])))
  refine WP.of_runBlock ⟨s₅, e₅, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₅, d₄.rd, rd₃'], by rw [wr₅, d₄.wr, wr₃']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain hsaved : ∀ i < 6, s₅.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₅ i hi', d₄.saved i hi', mem₃, keep₂ _ (by omega_using []) (by simp only [Core.ctrSlots]; omega_using [hroom, hi']), mem₁,
          sv₁ i hi']
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₅ _ (fun i hi' => by revert i; decide), d₄.rsp, rsp₃]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · have ht : (bytesAt s₀.mem P 16).length = 16 := by simp [bytesAt]
    rw [m₅, ctr32_of_dinv (cs.cipher_len k) ht d₄.data, gcmBlocks_eq s₃.mem, gcmBlocks_eq s₀.mem, mem₃,
      cbcBlocks_frame f₂ (hstk.coreFrame_disj (sDS.sub_right (Region.sub_prefix (by omega_using [hNs]))) ⟨_, hwD, fun _ h => h⟩),
      cbcBlocks_frame f₁' (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sDS
        · exact sPD.symm)]
    rfl
  · have pStk : ∀ x ∈ stkList c (s₀.gpr .rsp), Region.Disjoint ⟨P, 16⟩ x := hstk.disj ⟨_, hwP, fun _ h => h⟩
    refine ctr32_next ?_
    rw [m₅, bytesAt_frame d₄.frame (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact sPS
          · exact sPD
        · rw [rsp₃] at hx; exact pStk x hx) (by decide), mem₃,
      bytesAt_frame f₂ (coreFrame_disj (sPS.sub_right (Region.sub_prefix (by omega_using [hNs]))) pStk)
        (by decide), mem₁, bP₁, hn]
  · rw [m₅]
    refine ((f₁'.sub fun x hx => ⟨x, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₂.sub fun x hx => by
        obtain ⟨y, hy, hs⟩ := coreFrame_sub (rs := [⟨B, 8 * c.ctrSlots⟩])
          ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_using [hNs])⟩ x hx
        refine ⟨y, ?_, hs⟩
        rcases List.mem_append.mp hy with hy | hy
        · simp only [List.mem_singleton] at hy; subst hy; simp
        · exact List.mem_append_right _ hy)).trans ?_
    rw [← mem₃]
    exact d₄.frame.sub fun x hx => ⟨x, by
      rw [rsp₃] at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp
      · exact List.mem_append_right _ hx, fun _ h => h⟩

end VG.Proof.Modes.X86_64
