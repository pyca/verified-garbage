import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Proof.Modes.Counter

/-!
# CTR on x86-64: the counter blocks

The running counter block `V` (a number below `2¹²⁸`) is kept as two 64-bit
integers, `hiOf V` and `loOf V`. `incr_ok`: `add`, `adc` step it by one.
`ctrBlocks_ok`: the group's `G` counter blocks, `V … V + G - 1` as 16
big-endian bytes each, to the core's buffer, and `V + G` to the running
counter's slots.
-/

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
  obtain ⟨s₇, e₇, h₇, l₇, o₇, m₇, rd₇, wr₇⟩ := incr_ok s₆ (V := V) (by rw [g₆' _ (by decide), hh])
    (by rw [g₆' _ (by decide), hl])
  have hP : wordAddr B (c.buf + 2 * b) = bufAddr c B b := by
    simp only [wordAddr, bufAddr]; congr 2; omega
  have hP1 : wordAddr B (c.buf + 2 * b + 1) = bufAddr c B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, bufAddr]; rw [addr_add]; congr 2; omega
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
  | 0, _, s, V, _, _, hh, hl => ⟨s, rfl, hh, hl, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl => by
    have hs := hL.small
    have hroom := hL.room
    have hbuf := hL.buf_le
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctrLoop_ok hL k (by omega) s V hB hw hh hl
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctrBlock_ok hL s₁ (V := V + k) (b := k) (by omega)
      (by rw [o₁ _ (by decide) (by decide) (by decide), hB]) (by rw [wr₁]; exact hw) h₁ l₁
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
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega
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
        (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega) (by simp only [Core.hiSlot, Core.loSlot] at hx ⊢; omega)
        (by simp only [Core.hiSlot] at hx ⊢; omega))
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
