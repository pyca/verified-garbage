module

public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.Modes.Counter
public import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Modes.X86_64.Counter`, which this module and modules that import it used -/

section

/-!
# CTR on x86-64: the counter blocks

The running counter block `V` (a number below `2¹²⁸`) is kept as two 64-bit
integers, `hiOf V` and `loOf V`. `incr_ok`: `add`, `adc` step it by one.
`ctrBlocks_ok`: the group's `G` counter blocks, `V … V + G - 1` as 16
big-endian bytes each, to the core's buffer, and `V + G` to the running
counter's slots.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

theorem incr_vals (V : Nat) :
    loOf V + (1 : BitVec 32).signExtend 64 = loOf (V + 1) ∧
    hiOf V + (0 : BitVec 32).signExtend 64 +
        (BitVec.ofBool (decide (2 ^ 64 ≤ (loOf V).toNat + ((1 : BitVec 32).signExtend 64).toNat))).setWidth 64 =
      hiOf (V + 1) := by
  have e1 : ((1 : BitVec 32).signExtend 64) = BitVec.ofNat 64 1 := rfl
  have e0 : ((0 : BitVec 32).signExtend 64) = BitVec.ofNat 64 0 := rfl
  obtain ⟨h1, h2⟩ := carry_vals V 1 (by decide)
  refine ⟨by rw [e1, h1], ?_⟩
  rw [e0, e1, BitVec.add_zero, ← h2]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 1).toNat) <;> rfl

/-- `add rbx, 1; adc rax, 0`: the running counter stepped by one. -/
theorem incr_ok (s : State) {V : Nat} (hh : s.gpr .rax = hiOf V) (hl : s.gpr .rbx = loOf V) :
    ∃ s', runBlock isa [.alu .add .rbx (.imm 1), .alu .adc .rax (.imm 0)] s = some s' ∧
      s'.gpr .rax = hiOf (V + 1) ∧ s'.gpr .rbx = loOf (V + 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨i1, i2⟩ := incr_vals V
  let e1 := (1 : BitVec 32).signExtend 64
  let e0 := (0 : BitVec 32).signExtend 64
  let c := decide (2 ^ 64 ≤ (s.gpr .rbx).toNat + e1.toNat)
  let s₁ := (arithFlags s (s.gpr .rbx + e1) c (addOverflow (s.gpr .rbx) e1 (s.gpr .rbx + e1))).setReg .rbx
    (s.gpr .rbx + e1)
  let r := s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (2 ^ 64 ≤ (s₁.gpr .rax).toNat + e0.toNat + c.toNat))
    (addOverflow (s₁.gpr .rax) e0 r)).setReg .rax r
  have g₁ : ∀ x, x ≠ .rbx → s₁.gpr x = s.gpr x := fun x hx => by
    simp only [s₁, RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_arithFlags]
  refine ⟨s₂, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.map_some]
    rfl
  · show s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64 = _
    rw [g₁ .rax (by decide), hh]
    simp only [c, hl]
    exact i2
  · show (s₂.gpr .rbx) = _
    simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ Reg.rax by decide), RegUpd.gpr_arithFlags, s₁,
      RegUpd.gpr_setReg_self, hl]
    exact i1
  · simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, g₁ _ h2]

theorem ctrBlock_eq (c : Core) (b : Nat) : c.ctrBlock b =
    ([movR .rcx .rax] : List Instr) ++ (([.bswap .rcx] : List Instr) ++ (([st (c.buf + 2 * b) .rcx] : List Instr) ++
      (([movR .rcx .rbx] : List Instr) ++ (([.bswap .rcx] : List Instr) ++
      (([st (c.buf + 2 * b + 1) .rcx] : List Instr) ++
      ([.alu .add .rbx (.imm 1), .alu .adc .rax (.imm 0)] : List Instr)))))) := rfl

variable {c : Core}

/-- Counter block `b` to the buffer, and the running counter stepped. -/
theorem ctrBlock_ok (hL : Layout c) (s : State) {B : Addr} {V b : Nat} (hb : b < c.G) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr) (hh : s.gpr .rax = hiOf V) (hl : s.gpr .rbx = loOf V) :
    ∃ s', runBlock isa (c.ctrBlock b) s = some s' ∧
      s'.gpr .rax = hiOf (V + 1) ∧ s'.gpr .rbx = loOf (V + 1) ∧
      bytesAt s'.mem (bufAddr c B b) 16 = Spec.Ctr.ofNat V 16 ∧
      Frame [⟨bufAddr c B b, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  have h0 : c.buf + 2 * b < c.ctrSlots := by simp only [Core.ctrSlots]; omega_arith
  have h1 : c.buf + 2 * b + 1 < c.ctrSlots := by simp only [Core.ctrSlots]; omega_arith
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
  obtain ⟨s₇, e₇, h₇, l₇, o₇, m₇, rd₇, wr₇⟩ := incr_ok s₆ (V := V) (by rw [g₆' _ (by decide), hh])
    (by rw [g₆' _ (by decide), hl])
  have hP : wordAddr B (c.buf + 2 * b) = bufAddr c B b := by
    simp only [wordAddr, bufAddr]; congr 2; omega_arith
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega_arith
  have hmem : s₇.mem = (s.mem.writeW (wordAddr B (c.buf + 2 * b)) (bswap64 (hiOf V))).writeW
      (wordAddr B (c.buf + 2 * b + 1)) (bswap64 (loOf V)) := by
    rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁, r₅, r₄, g₃, r₂, r₁, hh, o₂ .rbx (by decide), o₁ .rbx (by decide), hl]
  rw [hP, hP1] at hmem
  refine ⟨s₇, ?_, h₇, l₇, by rw [hmem]; exact bytes_pair _ _ _, ?_, fun r h1 h2 h3 => by rw [o₇ r h1 h2, g₆' r h3],
    by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctrBlock_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, e₇]
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
    (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr → s.gpr .rax = hiOf V → s.gpr .rbx = loOf V →
    ∃ s', runBlock isa ((List.range k).flatMap c.ctrBlock) s = some s' ∧
      s'.gpr .rax = hiOf (V + k) ∧ s'.gpr .rbx = loOf (V + k) ∧
      (∀ j < k, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      Frame [bufPrefix c B k] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, V, _, _, hh, hl => ⟨s, rfl, hh, hl, fun j hj => by omega_arith, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl => by
    have hs := hL.small
    have hroom := hL.room
    have hbuf := hL.buf_le
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctrLoop_ok hL k (by omega_arith) s V hB hw hh hl
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctrBlock_ok hL s₁ (V := V + k) (b := k) (by omega_arith)
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
    refine ⟨s₂, ?_, by rw [h₂, Nat.add_assoc], by rw [l₂, Nat.add_assoc], fun j hj => ?_, ?_,
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

/-- The running counter's slots. -/
abbrev ctrRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.hiSlot), 16⟩

/-- The group's `G` counter blocks `V … V + G - 1` to the buffer, and the
running counter stepped to `V + G`. -/
theorem ctrBlocks_ok (hL : Layout c) (s : State) {B : Addr} {V : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr)
    (hh : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf V) (hl : s.mem.readW (wordAddr B c.loSlot) 64 = loOf V) :
    ∃ s', runBlock isa c.ctrBlocks s = some s' ∧
      (∀ j < c.G, bytesAt s'.mem (bufAddr c B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (V + c.G) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (V + c.G) ∧
      Frame [bufRegion c B, ctrRegion c B] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega_arith
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega_arith
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (s := s) (b := B) (k := c.hiSlot) .rax hB
    (inRd (slot_wr hw hN hH))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movS_ok (s := s₁) (b := B) (k := c.loSlot) .rbx
    (by rw [o₁ _ (by decide), hB]) (by rw [rd₁, wr₁]; exact inRd (slot_wr hw hN hLo))
  obtain ⟨s₃, e₃, h₃, l₃, b₃, f₃, o₃, rd₃, wr₃⟩ := ctrLoop_ok hL (B := B) c.G (Nat.le_refl _) s₂ V
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hB]) (by rw [wr₂, wr₁]; exact hw)
    (by rw [o₂ _ (by decide), v₁, hh]) (by rw [v₂, m₁, hl])
  have hB₃ : s₃.gpr sb = B := by
    rw [o₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (s := s₃) (b := B) (k := c.hiSlot) .rax hB₃
    (by rw [wr₃, wr₂, wr₁]; exact slot_wr hw hN hH)
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := B) (k := c.loSlot) .rbx (by rw [g₄]; exact hB₃)
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hN hLo)
  have hmem : s₅.mem = (s₃.mem.writeW (wordAddr B c.hiSlot) (hiOf (V + c.G))).writeW (wordAddr B c.loSlot)
      (loOf (V + c.G)) := by
    rw [m₅, m₄, g₄, h₃, l₃]
  have fC : Frame [ctrRegion c B] s₃.mem s₅.mem := by
    rw [hmem]
    have hm : ctrRegion c B ∈ [ctrRegion c B] := List.mem_singleton_self _
    have hc := fun (x : Nat) (hx : x = c.hiSlot ∨ x = c.loSlot) =>
      (VG.Offset.contains B (d := 8 * x) (n := 64 / 8) (e := 8 * c.hiSlot) (k := 16)
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_arith) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega_arith)
        (by simp only [Core.hiSlot] at hx ⊢; omega_arith))
    exact ((Frame.refl _ _).writeW hm _ (hc _ (.inl rfl))).writeW hm _ (hc _ (.inr rfl))
  refine ⟨s₅, ?_, fun j hj => ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.ctrBlocks, runBlock_app, runBlock_app,
      show ([movS .rax c.hiSlot, movS .rbx c.loSlot] : List Instr) = [movS .rax c.hiSlot] ++ [movS .rbx c.loSlot]
        from rfl,
      runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      show ([st c.hiSlot .rax, st c.loSlot .rbx] : List Instr) = [st c.hiSlot .rax] ++ [st c.loSlot .rbx] from rfl,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [bytesAt_frame fC (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega_arith) (by omega_arith)
        (by simp only [Core.hiSlot]; omega_arith)) (by decide)]
    exact b₃ j hj
  · rw [hmem, readW_slot_write _ (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₃' : Frame [bufRegion c B] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact f₃
    exact (f₃'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · rw [g₅, g₄, o₃ r h1 h2 h3, o₂ r h2, o₁ r h1]

end VG.Proof.Modes.X86_64

end

end

/-! ### `Modes.X86_64.Xor`, which this module and modules that import it used -/

section

/-!
# XORing blocks on x86-64

`xorBlocks_wp`: the loop `xorBlocks` XORs `c ≥ 1` blocks of 16 bytes at
`rax` into those at `rbx` (areas that do not overlap), through `rbp`,
counting down `rcx`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64

/-- `mov rbp, [rax + d]; xor rbp, [rbx + d]; mov [rbx + d], rbp`. -/
theorem xorWord_ok (s : State) (d : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 d) 8)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rbp (.mem (at_ .rax d)), .alu .xor .rbp (.mem (at_ .rbx d)),
        .store (at_ .rbx d) .rbp] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d)
        (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64 ^^^ s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64 ^^^ s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64
  let s₁ := s.setReg .rbp (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64)
  let s₂ := (arithFlags s₁ v false false).setReg .rbp v
  refine ⟨{ s₂ with mem := s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) v }, ?_, rfl,
    fun r hr => ?_, rfl, rfl⟩
  · simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.store64,
      State.ea, ofInt_nat, hr, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ .rbp by decide), RegUpd.wr_setReg, RegUpd.rd_setReg,
      RegUpd.mem_setReg, hr', hw, RegUpd.wr_arithFlags, RegUpd.rd_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.gpr_arithFlags]
    rfl
  · show s₂.gpr r = _
    simp only [s₂, s₁, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- XORing, after `j` of `c` blocks. -/
structure XorInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = A + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = B + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (c - j)
  xored : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) =
    s₀.mem (A + BitVec.ofNat 64 t) ^^^ s₀.mem (B + BitVec.ofNat 64 t)
  rest : ∀ t, 16 * j ≤ t → t < 16 * c → s.mem (B + BitVec.ofNat 64 t) = s₀.mem (B + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c < 2 ^ 59)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : XorInv A B c s₀ 0 s₀) :
    WP isa Core.xorBlocks s₀ (XorInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ XorInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain hA0 := hA (2 * j) (by omega_arith)
  obtain hA1 := hA (2 * j + 1) (by omega_arith)
  obtain hB0 := hB (2 * j) (by omega_arith)
  obtain hB1 := hB (2 * j + 1) (by omega_arith)
  obtain hn : 16 * c < 2 ^ 64 := by omega_arith
  obtain hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain rB : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ e, e < 2 * c →
      InRegions (st.rd ++ st.wr) (B + BitVec.ofNat 64 (8 * e)) 8 := fun st h1 h2 e he => by
    rw [h1, h2]; exact (let ⟨r, hr, hc⟩ := hB e he; ⟨r, List.mem_append_right _ hr, hc⟩)
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := xorWord_ok s 0
    (by rw [hi.rd, hi.wr, hi.rax, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact rB s hi.rd hi.wr _ (by omega_arith))
    (by rw [hi.wr, hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := xorWord_ok s₁ 8
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.rax, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]
        exact rB s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr) _ (by omega_arith))
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp] ++
      ([.mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp] ++
      ([.alu .add .rax (.imm 16)] ++ ([.alu .add .rbx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  obtain r1 : s₁.gpr .rbx = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  obtain a1 : s₁.gpr .rax = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  obtain hm : s₅.mem = s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64 ^^^ s₁.mem.readW (B + BitVec.ofNat 64 (16 * j + 8)) 64) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  obtain hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64 ^^^ s.mem.readW (B + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area, and on `B`'s beyond the first word.
  obtain hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_xor_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  obtain hB₁ : ∀ t, 16 * j + 8 ≤ t → t < 16 * c → s₁.mem (B + BitVec.ofNat 64 t) = s.mem (B + BitVec.ofNat 64 t) :=
    fun t h1 h2 => by
      rw [hm₁, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
  obtain hinv : XorInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t h1 h2 => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
        show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
        show c - j - 1 = c - (j + 1) by omega_arith]
    · rw [hm, writeW_xor_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          addr_add, show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hB₁ t h8 (by omega_arith),
          hAs t (by omega_arith), hi.rest t (by omega_arith) (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_xor_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            addr_add, show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith), hi.rest t h0 (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.xored t (by omega_arith)
    · rw [hm, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)),
        hB₁ t (by omega_arith) h2, hi.rest t (by omega_arith) h2]
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_xor_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_xor_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith
  by_cases hl : j + 1 = c
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega_arith, c - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hinv⟩

end VG.Proof.Modes.X86_64

end

end

/-!
# One group of blocks of CTR on x86-64, for any core

`ctrGroup_wp`: one iteration of the data loop writes the group's `G`
counter blocks to the core's buffer (`ctrBlocks_ok`), encrypts them there
(`CoreSpec.crypt_wp`), XORs the first `min(G, left)` into the group's blocks
(`xorBlocks_wp`) and steps to the next group. Block `j` of the data becomes
CTR's output block `j` (`ctrOut`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- `rcx := min(left, G)`. -/
theorem groupCount_wp (hG : c.G < 2 ^ 31) (hlc : c.leftReg ≠ .rcx) {s : State} {v : Nat}
    (hv : s.gpr c.leftReg = BitVec.ofNat 64 v) (hv64 : v < 2 ^ 64) :
    WP isa c.groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v c.G) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s .rcx (BitVec.ofNat 64 c.G)
  obtain ⟨s₃, e₃, f₃, g₃, m₃, rd₃, wr₃⟩ := cmpImm_ok s₂ c.leftReg (BitVec.ofNat 32 c.G) (v := v) (K := c.G)
    (by rw [o₂ _ hlc, hv]) hv64 (by rw [signExtend_small hG, BitVec.toNat_ofNat]; omega_using [hG])
  unfold Core.groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [show ([.movImm64 .rcx (BitVec.ofNat 64 c.G), .alu .cmp c.leftReg (.imm (BitVec.ofNat 32 c.G))] : List Instr) =
        [.movImm64 .rcx (BitVec.ofNat 64 c.G)] ++ [.alu .cmp c.leftReg (.imm (BitVec.ofNat 32 c.G))] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  refine WP.ite (decide (v < c.G)) (by simp [X86_64.eval, f₃]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rcx c.leftReg
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 => ?_, by rw [m₄, m₃, m₂], by rw [rd₄, rd₃, rd₂],
      by rw [wr₄, wr₃, wr₂]⟩
    · rw [r₄, g₃, o₂ _ hlc, hv, Nat.min_eq_left (by simp at h; omega_using [h])]
    · rw [o₄ r h1, g₃, o₂ r h1]
  · refine WP.of_runBlock ⟨s₃, rfl, ?_, fun r h1 => ?_, by rw [m₃, m₂], by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    · rw [g₃, r₂, Nat.min_eq_right (by simp at h; omega_using [h])]
    · rw [g₃, o₂ r h1]

/-- The buffer's address to `rax`, the data's to `rbx`, the count to `r10`. -/
theorem xorArgs_ok (hb : 8 * c.buf < 2 ^ 31) (hda : c.dataReg ≠ .rax) (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.xorArgs s = some s' ∧ s'.gpr .rax = B + BitVec.ofNat 64 (8 * c.buf) ∧
      s'.gpr .rbx = s.gpr c.dataReg ∧ s'.gpr .r10 = s.gpr .rcx ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rax (BitVec.ofNat 32 (8 * c.buf))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rbx c.dataReg
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .r10 .rcx
  refine ⟨s₄, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.xorArgs, show ([movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf))), movR .rbx c.dataReg,
        movR .r10 .rcx] : List Instr) = [movR .rax sb] ++ (([.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf)))] :
        List Instr) ++ (([movR .rbx c.dataReg] : List Instr) ++ [movR .r10 .rcx])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB, signExtend_small (by omega_using [hb])]
  · rw [o₄ _ (by decide), r₃, o₂ _ hda, o₁ _ hda]
  · rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  · rw [o₄ r h3, o₃ r h2, o₂ r h1, o₁ r h1]

/-- On past the group's blocks: the data's address from `rbx`, the count
from `r10` off the blocks left; ZF is set when none are left. -/
theorem advance_ok (hdl : c.dataReg ≠ c.leftReg) (hd10 : c.dataReg ≠ .r10) (s : State) :
    ∃ s', runBlock isa c.advance s = some s' ∧ s'.gpr c.dataReg = s.gpr .rbx ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - s.gpr .r10 ∧
      s'.zf = some (s.gpr c.leftReg - s.gpr .r10 == 0) ∧
      (∀ r, r ≠ c.dataReg → r ≠ c.leftReg → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg .rbx
  obtain ⟨s₂, e₂, r₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subReg_ok s₁ c.leftReg .r10
  obtain l₁ : s₁.gpr c.leftReg = s.gpr c.leftReg := o₁ _ (Ne.symm hdl)
  obtain t₁ : s₁.gpr .r10 = s.gpr .r10 := o₁ _ (Ne.symm hd10)
  refine ⟨s₂, ?_, by rw [o₂ _ hdl, r₁], by rw [r₂, l₁, t₁], by rw [z₂, l₁, t₁],
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [Core.advance, show ([movR c.dataReg .rbx, .alu .sub c.leftReg (.reg .r10)] : List Instr) =
    [movR c.dataReg .rbx] ++ [.alu .sub c.leftReg (.reg .r10)] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- What the data loop works on: the scratch buffer at `B`, the `n` blocks at
`D`. -/
structure GPre (c : Core) (s₀ : State) (B D : Addr) (n : Nat) (L : Nat := 16) : Prop where
  scr : ScrIn s₀ B c.ctrSlots
  dat : (⟨D, L * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, L * n⟩ ⟨B, 8 * c.ctrSlots⟩
  fitD : D.toNat + L * n ≤ 2 ^ 64
  stk : StkOk c s₀

/-- The data loop, before group `g`, from the counter block `V` with the key
`k`. -/
structure GInv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  hi : s.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (V + c.G * g)
  lo : s.mem.readW (wordAddr B c.loSlot) 64 = loOf (V + c.G * g)
  data : DInv 16 s₀.mem s.mem D n (c.G * g) (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (V : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv 16 s₀.mem s.mem D n n (ctrOut (cs.cipher k) s₀.mem D V)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 16 * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Byte `u` of the `L` at `p`. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {L u : Nat} (hu : u < L) :
    (bytesAt m p L).getD u 0 = m (p + BitVec.ofNat 64 u) := by
  simp [bytesAt, hu]

theorem ctrGroup_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {V : Nat}
    (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : GInv cs s₀ B D n k V g s) :
    WP isa c.ctrGroup s fun s' => (s'.zf = some true ∧ GDone cs s₀ B D n k V s') ∨
      (s'.zf = some false ∧ GInv cs s₀ B D n k V (g + 1) s') := by
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
  obtain ⟨s₁, e₁, tb₁, h₁, l₁, f₁, o₁, rd₁, wr₁⟩ := ctrBlocks_ok hL s hi.base hwS hi.hi hi.lo
  unfold Core.ctrGroup
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
  obtain hdata : DInv 16 s₀.mem s₆.mem D n (c.G * g + cc) (ctrOut (cs.cipher k) s₀.mem D V) := by
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
          (cs.cipher k (Spec.Ctr.ofNat (V + c.G * g + t / 16) 16)).getD (t % 16) 0 := by
        rw [eT, ← bytesAt_getD s₂.mem _ hu, ks₂ _ hj, tb₁ _ hj]
      obtain hd₂ : s₂.mem (A + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 i) := by
        rw [← e1, via₁₂ i hin, hi.data i hin, ite_eq_right (by omega_using [hin1])]
      rw [e1, h₅.xored _ (by omega_using [hin1]), mem₄, hks, hd₂, ite_eq_left (show i < 16 * (c.G * g + cc) by omega_using [hin1]),
        ctrOut_getD (cs.cipher_len k) _ _ _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega_using [],
        show V + c.G * g + t / 16 = V + i / 16 by omega_using [hin1], show t % 16 = i % 16 by omega_using [hin1], BitVec.xor_comm]
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
    · rw [hiSlot₆ _ (.inl rfl), h₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]
    · rw [hiSlot₆ _ (.inr rfl), l₁, show V + c.G * g + c.G = V + c.G * (g + 1) by rw [Nat.mul_succ]; omega_using []]

end VG.Proof.Modes.X86_64
