import VerifiedGarbage.Proof.Sm4.X86_64.GroupStep
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Impl.Sm4.X86_64.Ctr

/-!
# SM4-CTR on x86-64: the counter blocks

The running counter block `V` (a number below `2¹²⁸`) is kept as two 64-bit
integers, `hiOf V` and `loOf V`. `incr_ok`: `add`, `adc` step it by one.
`ctrBlocks_ok`: the group's sixteen counter blocks, `V … V + 15` as 16
big-endian bytes each, to the tail buffer, and `V + 16` to the running
counter's slots.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st at_)
open VG.Spec.Aes (bytesAt)

/-- The high and low halves of the counter block `V`. -/
def hiOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 (V / 2 ^ 64)
def loOf (V : Nat) : BitVec 64 := BitVec.ofNat 64 V

theorem incr_vals (V : Nat) :
    loOf V + (1 : BitVec 32).signExtend 64 = loOf (V + 1) ∧
    hiOf V + (0 : BitVec 32).signExtend 64 +
        (BitVec.ofBool (decide (2 ^ 64 ≤ (loOf V).toNat + ((1 : BitVec 32).signExtend 64).toNat))).setWidth 64 =
      hiOf (V + 1) := by
  have e1 : ((1 : BitVec 32).signExtend 64) = BitVec.ofNat 64 1 := rfl
  have e0 : ((0 : BitVec 32).signExtend 64) = BitVec.ofNat 64 0 := rfl
  refine ⟨by rw [e1, loOf, loOf, BitVec.ofNat_add], ?_⟩
  rw [e0, e1]
  apply BitVec.eq_of_toNat_eq
  simp only [hiOf, loOf, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  by_cases h : V % 2 ^ 64 + 1 = 2 ^ 64
  · rw [decide_eq_true (by omega)]
    simp only [Bool.toNat_true]
    have : (V + 1) / 2 ^ 64 = V / 2 ^ 64 + 1 := by omega
    rw [this]; omega
  · rw [decide_eq_false (by omega)]
    simp only [Bool.toNat_false]
    have : (V + 1) / 2 ^ 64 = V / 2 ^ 64 := by omega
    rw [this]; omega

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

theorem bswap_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.bswap r] s = some s' ∧ s'.gpr r = bswap64 (s.gpr r) ∧
      (∀ x, x ≠ r → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg r (bswap64 (s.gpr r)), by simp only [runBlock_cons, runStep_some, runBlock_nil, exec],
    RegUpd.gpr_setReg_self _ _ _, fun _ hx => RegUpd.gpr_setReg_of_ne _ _ hx, rfl, rfl, rfl⟩

/-- Slot `k` of the scratch buffer at `B` is writable. -/
theorem slot_wr {rs : List Region} {B : Addr} (h : (⟨B, 8 * slots⟩ : Region) ∈ rs) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr B k) 8 :=
  ⟨_, h, VG.Offset.contains_base B (by omega) (by rw [slots_eq] at hk; omega)⟩

/-- The address of block `b` of the tail buffer. -/
abbrev tailAddr (B : Addr) (b : Nat) : Addr := B + BitVec.ofNat 64 (8 * tailSlot + 16 * b)

/-- Bytes below a store. -/
theorem bytesAt_writeW_above (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {d n : Nat} (hn : n ≤ d)
    (hw : 0 < w / 8) (hd : d + w / 8 ≤ 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 d) v) P n = bytesAt m P n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, Mem.writeW]
  apply Mem.write_apply
  have := VG.Proof.Sm4.off_sub_not P (t := i) (e := d) (n := w / 8) (Or.inl (by omega)) (by omega) hw hd
  exact this

/-- `bytesAt` of the two words written at `P` and `P + 8`: the big-endian
bytes of `V`. -/
theorem bytes_pair (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW P (bswap64 (hiOf V))).writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append, bytesAt_writeW_above _ _ _ (by decide) (by decide)
      (by decide),
    show (bswap64 (hiOf V)) = AesCtr.rv64 (hiOf V) from rfl, AesCtr.bytesAt_writeW_rv64,
    show (bswap64 (loOf V)) = AesCtr.rv64 (loOf V) from rfl, AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

theorem ctrBlock_eq (b : Nat) : ctrBlock b =
    ([movR .rcx .rax] : List Instr) ++ (([.bswap .rcx] : List Instr) ++ (([st (tailAt b 0) .rcx] : List Instr) ++
      (([movR .rcx .rbx] : List Instr) ++ (([.bswap .rcx] : List Instr) ++ (([st (tailAt b 1) .rcx] : List Instr) ++
      ([.alu .add .rbx (.imm 1), .alu .adc .rax (.imm 0)] : List Instr)))))) := rfl

/-- Counter block `b` to the tail buffer, and the running counter stepped. -/
theorem ctrBlock_ok (s : State) {B : Addr} {V b : Nat} (hb16 : b < 16) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr) (hh : s.gpr .rax = hiOf V) (hl : s.gpr .rbx = loOf V) :
    ∃ s', runBlock isa (ctrBlock b) s = some s' ∧
      s'.gpr .rax = hiOf (V + 1) ∧ s'.gpr .rbx = loOf (V + 1) ∧
      bytesAt s'.mem (tailAddr B b) 16 = Spec.Ctr.ofNat V 16 ∧
      Frame [⟨tailAddr B b, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 : tailAt b 0 < slots := by simp only [tailAt, tailSlot_eq, slots_eq]; omega
  have h1 : tailAt b 1 < slots := by simp only [tailAt, tailSlot_eq, slots_eq]; omega
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rcx .rax
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ .rcx
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stReg_ok (s := s₂) (b := B) (k := tailAt b 0) .rcx
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hB]) (by rw [wr₂, wr₁]; exact slot_wr hw h0)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rcx .rbx
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := bswap_ok s₄ .rcx
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stReg_ok (s := s₅) (b := B) (k := tailAt b 1) .rcx
    (by rw [o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hB])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw h1)
  have g₆' : ∀ r, r ≠ .rcx → s₆.gpr r = s.gpr r := fun r hr => by
    rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]
  obtain ⟨s₇, e₇, h₇, l₇, o₇, m₇, rd₇, wr₇⟩ := incr_ok s₆ (V := V) (by rw [g₆' _ (by decide), hh])
    (by rw [g₆' _ (by decide), hl])
  have hP : wordAddr B (tailAt b 0) = tailAddr B b := by
    simp only [wordAddr, tailAt, tailAddr]; congr 2; omega
  have hP1 : wordAddr B (tailAt b 1) = tailAddr B b + BitVec.ofNat 64 8 := by
    simp only [wordAddr, tailAt, tailAddr]; rw [addr_add]; congr 2; omega
  have hmem : s₇.mem = (s.mem.writeW (wordAddr B (tailAt b 0)) (bswap64 (hiOf V))).writeW
      (wordAddr B (tailAt b 1)) (bswap64 (loOf V)) := by
    rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁, r₅, r₄, g₃, r₂, r₁, hh, o₂ .rbx (by decide), o₁ .rbx (by decide), hl]
  rw [hP, hP1] at hmem
  refine ⟨s₇, ?_, h₇, l₇, by rw [hmem]; exact bytes_pair _ _ _, ?_, fun r h1 h2 h3 => by rw [o₇ r h1 h2, g₆' r h3],
    by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctrBlock_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, e₇]
  · rw [hmem]
    have hm : (⟨tailAddr B b, 16⟩ : Region) ∈ [(⟨tailAddr B b, 16⟩ : Region)] := List.mem_singleton_self _
    have c0 : (⟨tailAddr B b, 16⟩ : Region).Contains (tailAddr B b) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have c8 : (⟨tailAddr B b, 16⟩ : Region).Contains (tailAddr B b + BitVec.ofNat 64 8) (64 / 8) := by
      simp only [Region.Contains, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide
    exact ((Frame.refl _ _).writeW hm _ c0).writeW hm _ c8

/-- Bytes outside a frame. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact hf.bytes (R := ⟨p, n⟩) hd hn h₁

/-- The tail buffer's first `k` blocks. -/
abbrev tailRegion (B : Addr) (k : Nat) : Region := ⟨B + BitVec.ofNat 64 (8 * tailSlot), 16 * k⟩

/-- The first `k` counter blocks to the tail buffer. -/
theorem ctrLoop_ok {B : Addr} : ∀ (k : Nat), k ≤ 16 → ∀ (s : State) (V : Nat), s.gpr sb = B →
    (⟨B, 8 * slots⟩ : Region) ∈ s.wr → s.gpr .rax = hiOf V → s.gpr .rbx = loOf V →
    ∃ s', runBlock isa ((List.range k).flatMap ctrBlock) s = some s' ∧
      s'.gpr .rax = hiOf (V + k) ∧ s'.gpr .rbx = loOf (V + k) ∧
      (∀ j < k, bytesAt s'.mem (tailAddr B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      Frame [tailRegion B k] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, V, _, _, hh, hl => ⟨s, rfl, hh, hl, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | k + 1, hk, s, V, hB, hw, hh, hl => by
    have l₀ := tailSlot_eq
    obtain ⟨s₁, e₁, h₁, l₁, b₁, f₁, o₁, rd₁, wr₁⟩ := ctrLoop_ok k (by omega) s V hB hw hh hl
    obtain ⟨s₂, e₂, h₂, l₂, b₂, f₂, o₂, rd₂, wr₂⟩ := ctrBlock_ok s₁ (V := V + k) (b := k) (by omega)
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
    · refine (f₁.sub fun r hr => ⟨tailRegion B (k + 1), List.mem_singleton_self _, ?_⟩).trans
        (f₂.sub fun r hr => ⟨tailRegion B (k + 1), List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega) (by omega)

theorem ctrHi_eq : ctrHi = 390 := rfl
theorem ctrLo_eq : ctrLo = 391 := rfl

/-- The running counter's slots. -/
abbrev ctrRegion (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * ctrHi), 16⟩

/-- The group's sixteen counter blocks `V … V + 15` to the tail buffer, and
the running counter stepped to `V + 16`. -/
theorem ctrBlocks_ok (s : State) {B : Addr} {V : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr)
    (hh : s.mem.readW (wordAddr B ctrHi) 64 = hiOf V) (hl : s.mem.readW (wordAddr B ctrLo) 64 = loOf V) :
    ∃ s', runBlock isa ctrBlocks s = some s' ∧
      (∀ j < 16, bytesAt s'.mem (tailAddr B j) 16 = Spec.Ctr.ofNat (V + j) 16) ∧
      s'.mem.readW (wordAddr B ctrHi) 64 = hiOf (V + 16) ∧ s'.mem.readW (wordAddr B ctrLo) 64 = loOf (V + 16) ∧
      Frame [tailRegion B 16, ctrRegion B] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hH : ctrHi < slots := by decide
  have hL : ctrLo < slots := by decide
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (s := s) (b := B) (k := ctrHi) .rax hB
    (inRd (slot_wr hw hH))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movS_ok (s := s₁) (b := B) (k := ctrLo) .rbx
    (by rw [o₁ _ (by decide), hB]) (by rw [rd₁, wr₁]; exact inRd (slot_wr hw hL))
  obtain ⟨s₃, e₃, h₃, l₃, b₃, f₃, o₃, rd₃, wr₃⟩ := ctrLoop_ok (B := B) 16 (by decide) s₂ V
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hB]) (by rw [wr₂, wr₁]; exact hw)
    (by rw [o₂ _ (by decide), v₁]; show s.mem.readW (wordAddr (s.gpr sb) ctrHi) 64 = _; rw [hB, hh])
    (by rw [v₂]; show s₁.mem.readW (wordAddr (s₁.gpr sb) ctrLo) 64 = _; rw [m₁, o₁ _ (by decide), hB, hl])
  have hB₃ : s₃.gpr sb = B := by
    rw [o₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (s := s₃) (b := B) (k := ctrHi) .rax hB₃
    (by rw [wr₃, wr₂, wr₁]; exact slot_wr hw hH)
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := B) (k := ctrLo) .rbx (by rw [g₄]; exact hB₃)
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact slot_wr hw hL)
  have hw₃ : (⟨B, 8 * slots⟩ : Region) ∈ s₃.wr := by rw [wr₃, wr₂, wr₁]; exact hw
  have hmem : s₅.mem = (s₃.mem.writeW (wordAddr B ctrHi) (hiOf (V + 16))).writeW (wordAddr B ctrLo)
      (loOf (V + 16)) := by
    rw [m₅, m₄, g₄, h₃, l₃]
  have fC : Frame [ctrRegion B] s₃.mem s₅.mem := by
    rw [hmem]
    have hm : ctrRegion B ∈ [ctrRegion B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by decide) (by decide) (by decide))).writeW hm _
      (VG.Offset.contains B (by decide) (by decide) (by decide))
  refine ⟨s₅, ?_, fun j hj => ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [ctrBlocks, runBlock_app, runBlock_app,
      show ([movS .rax ctrHi, movS .rbx ctrLo] : List Instr) = [movS .rax ctrHi] ++ [movS .rbx ctrLo] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      show ([st ctrHi .rax, st ctrLo .rbx] : List Instr) = [st ctrHi .rax] ++ [st ctrLo .rbx] from rfl,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [bytesAt_frame fC (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by simp only [tailSlot_eq, ctrHi_eq]; omega) (by rw [tailSlot_eq]; omega)
        (by decide)) (by decide)]
    exact b₃ j hj
  · rw [hmem, readW_slot_write _ hH hL, ite_eq_right (by decide), Mem.readW_writeW_self64]
  · rw [hmem, Mem.readW_writeW_self64]
  · have f₃' : Frame [tailRegion B 16] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact f₃
    exact (f₃'.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fC.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · rw [g₅, g₄, o₃ r h1 h2 h3, o₂ r h2, o₁ r h1]

end VG.Proof.Sm4.X86_64
