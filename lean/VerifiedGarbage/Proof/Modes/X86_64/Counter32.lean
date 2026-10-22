module

public import VerifiedGarbage.Proof.Modes.X86_64.Counter
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr32
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

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
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have h0 : c.buf + 2 * b < c.ctrSlots := by simp only [Core.ctrSlots]; omega
  have h1 : c.buf + 2 * b + 1 < c.ctrSlots := by simp only [Core.ctrSlots]; omega
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
    simp only [wordAddr, bufAddr]; congr 2; omega
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega
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
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctr32Loop_ok hL k (by omega) s V hB hw hh hl
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctr32Block_ok hL s₁ (V := ctr32Val V k) (b := k) (by omega)
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
    refine ⟨s₂, ?_, by rw [h₂, ctr32Val_add], by rw [l₂, ctr32Val_add], fun j hj => ?_, ?_,
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
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega
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
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega)
        (by simp only [Core.hiSlot] at hx ⊢; omega))
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
      exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega)
        (by simp only [Core.hiSlot]; omega)) (by decide)]
    exact b₃ j hj
  · rw [hmem, readW_slot_write _ (by simp only [Core.hiSlot]; omega) (by simp only [Core.loSlot]; omega),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₃' : Frame [bufRegion c B] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact f₃
    exact (f₃'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · rw [g₅, g₄, o₃ r h1 h2 h3, o₂ r h2, o₁ r h1]

end VG.Proof.Modes.X86_64
