import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Proof.X448.X86_64.Verified
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseBits`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the bits of the scalar

`bits` stores bit `j` of byte `i` of the 57-byte scalar at byte `8i + j` of
`BITS`, so byte `t` of `BITS` is bit `t` of the scalar. The proof is X448's
(`Proof/X448/X86_64/Bits.lean`), for 57 bytes and without the clamping.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside ofs ofs_off' contains_sc bitJ addr_bit ea_bitAt
  ea_scalar bit_byte writeW8_apply writeW8_outside off_eq_iff inc_eq)
open VG.Impl.X448.X86_64 (BITS bitAt)

theorem bitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ j)) s fun s' =>
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base (BITS + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have w : InRegions s.wr (off base (BITS + (8 * i + j))) 1 :=
    ⟨_, hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have e := bit_byte b j hj
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.store8, ea_bitAt, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, hs.rdi, hb, ha, addr_bit, w, ite_false, reduceCtorEq, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; rfl
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, execShift, State.store8,
    ea_bitAt, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, ha, addr_bit, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩,
    ite_true, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_self]
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]

theorem bitsBody_eq : bitsBody = ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (bitJ 0 ++ (bitJ 1 ++ (bitJ 2 ++ (bitJ 3 ++ (bitJ 4 ++ (bitJ 5 ++ (bitJ 6 ++ (bitJ 7 ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 57)] : List Instr))))))))) := rfl

theorem cmp57 : ∀ i < 57,
    (BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (57 : BitVec 32) == 0) = decide (i + 1 = 57) := by
  decide +kernel

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    {i : Nat} (hi : i < 57) (hb : s.gpr .rbx = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 i) 1) :
    WP isa (.block bitsBody) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = 57)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ j < 8, s'.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem s'.mem := by
  rw [VG.Proof.Ed448.X86_64.bitsBody_eq, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun s' => s'.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_scalar s hk hb, State.load8, hkr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s₀ ⟨a0, g0, m0, rd0, wr0⟩ => ?_
  have hs₀ : Scr s₀ base := ⟨(g0 _ (by decide)).trans hs.rdi, wr0 ▸ hs.wr, hs.nowrap⟩
  have hb₀ : s₀.gpr .rbx = BitVec.ofNat 64 i := (g0 _ (by decide)).trans hb
  have keep : ∀ {x y : State}, (∀ r, r ≠ .rdx → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr →
      Scr x base → x.gpr .rbx = BitVec.ofNat 64 i → x.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 →
      Scr y base ∧ y.gpr .rbx = BitVec.ofNat 64 i ∧ y.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 :=
    fun g _ wr hx hbx hax => ⟨⟨(g _ (by decide)).trans hx.rdi, wr ▸ hx.wr, hx.nowrap⟩,
      (g _ (by decide)).trans hbx, (g _ (by decide)).trans hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₀ hi hb₀ a0 (j := 0) (by omega)) fun s₁ ⟨g1, rd1, wr1, m1⟩ => ?_
  obtain ⟨hs₁, hb₁, ha₁⟩ := keep g1 rd1 wr1 hs₀ hb₀ a0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₁ hi hb₁ ha₁ (j := 1) (by omega)) fun s₂ ⟨g2, rd2, wr2, m2⟩ => ?_
  obtain ⟨hs₂, hb₂, ha₂⟩ := keep g2 rd2 wr2 hs₁ hb₁ ha₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₂ hi hb₂ ha₂ (j := 2) (by omega)) fun s₃ ⟨g3, rd3, wr3, m3⟩ => ?_
  obtain ⟨hs₃, hb₃, ha₃⟩ := keep g3 rd3 wr3 hs₂ hb₂ ha₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₃ hi hb₃ ha₃ (j := 3) (by omega)) fun s₄ ⟨g4, rd4, wr4, m4⟩ => ?_
  obtain ⟨hs₄, hb₄, ha₄⟩ := keep g4 rd4 wr4 hs₃ hb₃ ha₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₄ hi hb₄ ha₄ (j := 4) (by omega)) fun s₅ ⟨g5, rd5, wr5, m5⟩ => ?_
  obtain ⟨hs₅, hb₅, ha₅⟩ := keep g5 rd5 wr5 hs₄ hb₄ ha₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₅ hi hb₅ ha₅ (j := 5) (by omega)) fun s₆ ⟨g6, rd6, wr6, m6⟩ => ?_
  obtain ⟨hs₆, hb₆, ha₆⟩ := keep g6 rd6 wr6 hs₅ hb₅ ha₅
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₆ hi hb₆ ha₆ (j := 6) (by omega)) fun s₇ ⟨g7, rd7, wr7, m7⟩ => ?_
  obtain ⟨hs₇, hb₇, ha₇⟩ := keep g7 rd7 wr7 hs₆ hb₆ ha₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitJ_ok hs₇ hi hb₇ ha₇ (j := 7) (by omega)) fun s₈ ⟨g8, rd8, wr8, m8⟩ => ?_
  obtain ⟨hs₈, hb₈, ha₈⟩ := keep g8 rd8 wr8 hs₇ hb₇ ha₇
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₈, inc_eq,
    ite_true, RegUpd.zf_arithFlags, RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, VG.Proof.Ed448.X86_64.cmp57 i hi]
  have hm : s₀.mem = s.mem := m0
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ite_eq_right hr.2.2, g8 r hr.2.1, g7 r hr.2.1, g6 r hr.2.1, g5 r hr.2.1, g4 r hr.2.1, g3 r hr.2.1,
      g2 r hr.2.1, g1 r hr.2.1, g0 r hr.1]
  · rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0]
  · rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
    have ne : ∀ a b, a < 8 → b < 8 → a ≠ b →
        off base (BITS + (8 * i + a)) ≠ off base (BITS + (8 * i + b)) := by
      intro a b ha hb hab h
      rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)] at h
      omega
    have ne' : ∀ a b, a < 8 → b < 8 → a ≠ b →
        (off base (BITS + (8 * i + a)) = off base (BITS + (8 * i + b))) = False :=
      fun a b ha hb hab => eq_false (ne a b ha hb hab)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [writeW8_apply, ite_true, ne', ite_false]
  · intro x hx
    have hd : ∀ j < 8, ofs base x ≠ BITS + (8 * i + j) := fun j hj h => by omega
    have hb : ∀ j < 8, BITS + (8 * i + j) < 2 ^ 64 := fun j hj => by simp only [BITS]; omega
    rw [m8, m7, m6, m5, m4, m3, m2, m1, writeW8_outside _ _ _ (hb 7 (by omega)) (hd 7 (by omega)),
      writeW8_outside _ _ _ (hb 6 (by omega)) (hd 6 (by omega)),
      writeW8_outside _ _ _ (hb 5 (by omega)) (hd 5 (by omega)),
      writeW8_outside _ _ _ (hb 4 (by omega)) (hd 4 (by omega)),
      writeW8_outside _ _ _ (hb 3 (by omega)) (hd 3 (by omega)),
      writeW8_outside _ _ _ (hb 2 (by omega)) (hd 2 (by omega)),
      writeW8_outside _ _ _ (hb 1 (by omega)) (hd 1 (by omega)),
      writeW8_outside _ _ _ (hb 0 (by omega)) (hd 0 (by omega)), hm]

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  rsi : s.gpr .rsi = k
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.X86_64.BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) .ne) s fun s' => VG.Proof.Ed448.X86_64.BInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.Ed448.X86_64.BInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.X86_64.BInv base k s₀ s i) ?_ (57 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsBody_ok hb.scr hb.rsi hi hb.rbx (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', g', rd', wr', bits', o'⟩ => ?_
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.Ed448.X86_64.BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.rdi, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.rsi, b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

/-- `bits`: byte `t` of `BITS` is bit `t` of byte `t / 8` of the scalar, for
`t < 456`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1) := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      VG.Proof.Ed448.X86_64.BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, hk, rfl, fun r hr => ?_, rfl, rfl, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86_64.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  exact ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => h₂.bits t (by omega)⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseField`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: field programs

A list of field operations on the slots (`FOp`) runs as X448's verified
field arithmetic (`mulE`, `sqrE`, `addE`, `subE`), for any correct field
multiplications (`FieldOk`): the slots become the operations' evaluation
(`evalOps`), and nothing else changes but the registers `clob` and the
memory in `[64, 1648)`. What the doubling and the addition programs evaluate
to is target-independent (`Proof/Ed448/Formulas.lean`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk mulE sqrE addE subE)

theorem slot_idx {n : Nat} (h : n < 22) : Impl.X448.X86_64.slot n = Impl.X448.X86_64.slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (op : FOp) (hv : fopValid op) :
    WP isa (.block (fopCode fld op)) s fun t =>
      Keep base s t ∧ VG.Proof.X448.X86_64.E t.mem base = evalOp op (VG.Proof.X448.X86_64.E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, VG.Proof.Ed448.X86_64.slot_idx h1, VG.Proof.Ed448.X86_64.slot_idx h2, VG.Proof.Ed448.X86_64.slot_idx h3]
    exact mulE hf hs _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [fopCode, VG.Proof.Ed448.X86_64.slot_idx h1, VG.Proof.Ed448.X86_64.slot_idx h2]
    exact sqrE hf hs _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, VG.Proof.Ed448.X86_64.slot_idx h1, VG.Proof.Ed448.X86_64.slot_idx h2, VG.Proof.Ed448.X86_64.slot_idx h3]
    exact addE hs _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [fopCode, VG.Proof.Ed448.X86_64.slot_idx h1, VG.Proof.Ed448.X86_64.slot_idx h2, VG.Proof.Ed448.X86_64.slot_idx h3]
    exact subE hs _ _ _

include hf in
theorem fieldCode_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ VG.Proof.X448.X86_64.E t.mem base = evalOps ops (VG.Proof.X448.X86_64.E s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.fop_ok hf hs op (hv op List.mem_cons_self)) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (ht.scr hs))
      fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et, evalOps, evalOps, List.foldl_cons]⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseStep`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: one bit

`step`: the counter `rbx` counts down to the bit `t`; `R` (slots 0–2) is
doubled, `T = R + Q` computed into slots 3–5, and `T` swapped into `R` with
the mask of byte `t` of `BITS` (the bit). Only the slots, the product's
words, the counter and the registers `clob` change.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap ea_bits
  clob)
open VG.Impl.X448.X86_64 (BITS slot cswap)

theorem dec_ok (s : State) {t : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) :
    WP isa (.block ([.alu .sub .rbx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, hb',
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl,
    rfl, rfl⟩

theorem mask_bit : ∀ b < 2, BitVec.setWidth 64 (0 : BitVec 32) - (BitVec.ofNat 8 b).setWidth 64 =
    mask (decide (b = 1)) := by decide

theorem bitMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block bitMask) s fun s' =>
      s'.gpr .rcx = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.rdx, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  apply WP.of_runBlock
  simp only [bitMask, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load8, ea_bits hs.rdi hb, hin, hbit, ite_true, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed448.X86_64.mask_bit b hb2, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

theorem step_eq : VG.Impl.Ed448.X86_64.step fld = ([.alu .sub .rbx (.imm 1)] : List Instr) ++ (fieldCode fld doubleOps ++
    (fieldCode fld addOps ++ (bitMask ++ (cswap (VG.Impl.X448.X86_64.slot 0) (VG.Impl.X448.X86_64.slot 3) ++ (cswap (VG.Impl.X448.X86_64.slot 1) (VG.Impl.X448.X86_64.slot 4) ++
    (cswap (VG.Impl.X448.X86_64.slot 2) (VG.Impl.X448.X86_64.slot 5) ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))))))) := by
  simp only [VG.Impl.Ed448.X86_64.step, List.append_assoc]

/-- The slots after an iteration, for the bit `sw`. -/
def stepEnv (sw : Bool) (e : Env) : Env :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (evalOps addOps (evalOps doubleOps e))))

theorem testRbx_ok (s : State) (n : Nat) (hn : n < 456) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block ([.alu .test .rbx (.reg .rbx)] : List Instr)) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have e : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    have : ∀ n < 456, (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
      decide +kernel
    exact this n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb, e]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩

include hf in
/-- An iteration, for the bit `t` (`b`). -/
theorem step_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (VG.Impl.Ed448.X86_64.step fld)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Proof.X448.X86_64.Outside base 64 1584 s.mem s'.mem ∧
      VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.Ed448.X86_64.stepEnv (decide (b = 1)) (VG.Proof.X448.X86_64.E s.mem base) := by
  rw [VG.Proof.Ed448.X86_64.step_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.fieldCode_ok hf doubleOps doubleOps_valid hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.fieldCode_ok hf addOps addOps_valid hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have b3 : s3.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide)]; exact b1
  have hofs : Proof.X448.X86_64.ofs base (off base (BITS + t)) = BITS + t :=
    Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)
  have hout : Proof.X448.X86_64.ofs base (off base (BITS + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (BITS + t)) :=
    Or.inr (by rw [hofs]; simp only [BITS]; omega)
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b := by
    rw [k3.mem _ hout, k2.mem _ hout, m1, hbit]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.bitMask_ok hs3 ht b3 hb2 hbit3) fun s4 ⟨c4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs4 0 3 (by decide) c4) fun s5 ⟨k5, c5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs5 1 4 (by decide) (c5.trans c4)) fun s6 ⟨k6, c6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs6 2 5 (by decide) (c6.trans (c5.trans c4))) fun s7 ⟨k7, _, e7⟩ => ?_
  have b7 : s7.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), g4 _ (by decide)]
    exact b3
  refine WP.mono (VG.Proof.Ed448.X86_64.testRbx_ok s7 t ht b7) fun s' ⟨z', g', m', rd', wr'⟩ => ?_
  refine ⟨(g' _).trans b7, z', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [g', k7.gpr r hr.2, k6.gpr r hr.2, k5.gpr r hr.2, g4 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr.2 (h ▸ by decide), fun h => hr.2 (h ▸ by decide)⟩),
      k3.gpr r hr.2, k2.gpr r hr.2, g1 r hr.1]
  · rw [rd', k7.rd, k6.rd, k5.rd, rd4, k3.rd, k2.rd, rd1]
  · rw [wr', k7.wr, k6.wr, k5.wr, wr4, k3.wr, k2.wr, wr1]
  · rw [m', ← m1]
    exact ((k2.mem.trans k3.mem).trans (by rw [m4]; exact Proof.X448.X86_64.Outside.refl _ _ _ _)).trans
      ((k5.mem.trans k6.mem).trans k7.mem)
  · rw [m', e7, e6, e5, m4, e3, e2, m1]
    rfl

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the loop over the bits

After the bits above `n` (counting down from 456), `R` (slots 0–2) is the
reference ladder's point after those bits (`Proof.Ed448.ladder`): each
iteration doubles it and adds `B` when the next bit is set. `Q` (slots
8–10) stays the base point and slot 11 `d`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask opSwap clob Outside)
open VG.Impl.X448.X86_64 (BITS slot)

theorem stepEnv_pt (sw : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86_64.stepEnv sw e) 0 1 2 =
      if sw then addWith (e 11) (double (pt e 0 1 2)) (pt e 8 9 10) else double (pt e 0 1 2) := by
  cases sw <;> rfl

theorem stepEnv_q (sw : Bool) (e : Env) : pt (VG.Proof.Ed448.X86_64.stepEnv sw e) 8 9 10 = pt e 8 9 10 := by
  cases sw <;> rfl

theorem stepEnv_d (sw : Bool) (e : Env) : VG.Proof.Ed448.X86_64.stepEnv sw e 11 = e 11 := by
  cases sw <;> rfl

/-- One bit: the ladder's point after the bits above `t`, then after bit `t`. -/
theorem ladder_step {e : Env} {k t : Nat} (ht : t < 456)
    (hr : pt e 0 1 2 = ladder k (456 - (t + 1))) (hq : pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    pt (VG.Proof.Ed448.X86_64.stepEnv (decide ((k >>> t) &&& 1 = 1)) e) 0 1 2 = ladder k (456 - t) := by
  rw [VG.Proof.Ed448.X86_64.stepEnv_pt, hd, hq, addWith_d, hr, ladder_bit k ht]
  rfl

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure MInv (base : Addr) (k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  q : pt (VG.Proof.X448.X86_64.E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : VG.Proof.X448.X86_64.E s.mem base 11 = Spec.Ed448.d
  rep : pt (VG.Proof.X448.X86_64.E s.mem base) 0 1 2 = ladder k (456 - n)

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → VG.Proof.Ed448.X86_64.MInv base k s₀ n s →
      WP isa (.loop (.block (VG.Impl.Ed448.X86_64.step fld)) .ne) s fun s' => VG.Proof.Ed448.X86_64.MInv base k s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun s' => VG.Proof.Ed448.X86_64.MInv base k s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.X86_64.MInv base k s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb2 : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1) := by
    rw [hi.mem _ (Or.inr (by
      rw [Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega))]
    exact hbits t (by omega)
  refine WP.mono (VG.Proof.Ed448.X86_64.step_ok hf hi.scr (by omega) hi.rbx hb2 hbit)
    fun s' ⟨b', z', g', rd', wr', o', e'⟩ => ?_
  have inv : VG.Proof.Ed448.X86_64.MInv base k s₀ t s' := by
    refine ⟨⟨(g' _ (by decide)).trans hi.scr.rdi, wr' ▸ hi.scr.wr, hi.scr.nowrap⟩, b',
      fun r hr => (g' r hr).trans (hi.gpr r hr), rd'.trans hi.rd, wr'.trans hi.wr,
      hi.mem.trans o', ?_, ?_, ?_⟩
    · rw [e', VG.Proof.Ed448.X86_64.stepEnv_q]; exact hi.q
    · rw [e', VG.Proof.Ed448.X86_64.stepEnv_d]; exact hi.d
    · rw [e']; exact VG.Proof.Ed448.X86_64.ladder_step (by omega) hi.rep hi.q hi.d
  simp only [eval, z', Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseConst`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the constants

`consts`: the neutral point into slots 0–2, the base point into slots 8–10
and `d` into slot 11, each as its seven words stored by `stores`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keeps rv wv stores_E Outside)
open VG.Proof.X448 (toFe)
open VG.Impl.X448.X86_64 (W slot)

theorem loadWords_ok (s : State) (v : Nat) :
    WP isa (.block ((W.zip (words7 v)).map fun (r, x) => Instr.movImm64 r x)) s fun t =>
      rv t W = wv (words7 v) ∧ Keeps W s t := by
  apply WP.of_runBlock
  simp only [W, words7, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rv, wv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-- `constSlot i v`: slot `i` is `v`, if its seven words are `v`. -/
theorem constSlot_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) (v : Spec.X448.Fe)
    (hv : toFe (wv (words7 v.val)) = v) :
    WP isa (.block (constSlot i.val v)) s fun t =>
      VG.Proof.X448.X86_64.E t.mem base = Function.update (VG.Proof.X448.X86_64.E s.mem base) i v ∧ Outside base (slot i.val) 56 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [constSlot, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadWords_ok s v.val) fun a ⟨va, ka⟩ => ?_
  refine WP.mono (stores_E (hs.of_keeps ka (by decide)) i W rfl) fun t ⟨et, ot, gt, rdt, wrt⟩ =>
    ⟨by rw [et, va, hv, ka.2.1], by rw [← ka.2.1]; exact ot, fun r hr => (gt r).trans (ka.1 r hr),
      rdt.trans ka.2.2.1, wrt.trans ka.2.2.2⟩

theorem c0 : toFe (wv (words7 (0 : Spec.X448.Fe).val)) = 0 := by decide +kernel
theorem c1 : toFe (wv (words7 (1 : Spec.X448.Fe).val)) = 1 := by decide +kernel
theorem cBx : toFe (wv (words7 Spec.Ed448.basePoint.X.val)) = Spec.Ed448.basePoint.X := by
  decide +kernel
theorem cBy : toFe (wv (words7 Spec.Ed448.basePoint.Y.val)) = Spec.Ed448.basePoint.Y := by
  decide +kernel
theorem cd : toFe (wv (words7 Spec.Ed448.d.val)) = Spec.Ed448.d := by decide +kernel

theorem consts_eq : consts = constSlot (0 : Index).val 0 ++ (constSlot (1 : Index).val 1 ++
    (constSlot (2 : Index).val 1 ++ (constSlot (8 : Index).val Spec.Ed448.basePoint.X ++
    (constSlot (9 : Index).val Spec.Ed448.basePoint.Y ++ (constSlot (10 : Index).val 1 ++
    constSlot (11 : Index).val Spec.Ed448.d))))) := by
  simp only [consts, List.append_assoc]; rfl

/-- `consts`: `R` the neutral point, `Q` the base point, slot 11 `d`. -/
theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block consts) s fun t =>
      Proof.Ed448.pt (VG.Proof.X448.X86_64.E t.mem base) 0 1 2 = Spec.Ed448.identity ∧
      Proof.Ed448.pt (VG.Proof.X448.X86_64.E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      VG.Proof.X448.X86_64.E t.mem base 11 = Spec.Ed448.d ∧ Outside base 64 1584 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i : Index, 3 ≤ i.val → i.val < 8 ∨ 12 ≤ i.val → VG.Proof.X448.X86_64.E t.mem base i = VG.Proof.X448.X86_64.E s.mem base i) := by
  rw [VG.Proof.Ed448.X86_64.consts_eq]
  have step : ∀ {x : State} (i : Index) (v : Spec.X448.Fe), toFe (wv (words7 v.val)) = v →
      Scr x base → ∀ {rest : List Instr} {Q : State → Prop},
      (∀ y, VG.Proof.X448.X86_64.E y.mem base = Function.update (VG.Proof.X448.X86_64.E x.mem base) i v → Outside base 64 1584 x.mem y.mem →
        (∀ r, r ∉ W → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr → Scr y base →
        WP isa (.block rest) y Q) →
      WP isa (.block (constSlot i.val v ++ rest)) x Q := by
    intro x i v hv hx rest Q k
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86_64.constSlot_ok hx i v hv) fun y ⟨ey, oy, gy, rdy, wry⟩ =>
      k y ey (oy.mono (by simp only [slot]; omega) (by have := i.isLt; simp only [slot]; omega))
        gy rdy wry ⟨(gy _ (by decide)).trans hx.rdi, wry ▸ hx.wr, hx.nowrap⟩
  refine step 0 0 VG.Proof.Ed448.X86_64.c0 hs fun s1 e1 o1 g1 rd1 wr1 hs1 => ?_
  refine step 1 1 VG.Proof.Ed448.X86_64.c1 hs1 fun s2 e2 o2 g2 rd2 wr2 hs2 => ?_
  refine step 2 1 VG.Proof.Ed448.X86_64.c1 hs2 fun s3 e3 o3 g3 rd3 wr3 hs3 => ?_
  refine step 8 _ VG.Proof.Ed448.X86_64.cBx hs3 fun s4 e4 o4 g4 rd4 wr4 hs4 => ?_
  refine step 9 _ VG.Proof.Ed448.X86_64.cBy hs4 fun s5 e5 o5 g5 rd5 wr5 hs5 => ?_
  refine step 10 1 VG.Proof.Ed448.X86_64.c1 hs5 fun s6 e6 o6 g6 rd6 wr6 hs6 => ?_
  refine WP.mono (VG.Proof.Ed448.X86_64.constSlot_ok hs6 11 _ VG.Proof.Ed448.X86_64.cd) fun t ⟨et, ot, gt, rdt, wrt⟩ => ?_
  have O : Outside base 64 1584 s.mem t.mem :=
    o1.trans (o2.trans (o3.trans (o4.trans (o5.trans (o6.trans
      (ot.mono (by simp only [slot]; omega) (by simp only [slot]; omega)))))))
  refine ⟨?_, ?_, ?_, O, fun r hr => ?_, ?_, ?_, fun i h1 h2 => ?_⟩
  · rw [et, e6, e5, e4, e3, e2, e1]; rfl
  · rw [et, e6, e5, e4, e3, e2, e1]; rfl
  · simp only [et, Function.update_self]
  · rw [gt r hr, g6 r hr, g5 r hr, g4 r hr, g3 r hr, g2 r hr, g1 r hr]
  · rw [rdt, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wrt, wr6, wr5, wr4, wr3, wr2, wr1]
  · have ne : ∀ j : Index, j.val < 3 ∨ (8 ≤ j.val ∧ j.val < 12) → i ≠ j := fun j hj h => by
      subst h; omega
    rw [et, e6, e5, e4, e3, e2, e1, Function.update_of_ne (ne 11 (by decide)),
      Function.update_of_ne (ne 10 (by decide)), Function.update_of_ne (ne 9 (by decide)),
      Function.update_of_ne (ne 8 (by decide)), Function.update_of_ne (ne 2 (by decide)),
      Function.update_of_ne (ne 1 (by decide)), Function.update_of_ne (ne 0 (by decide))]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarWord`. -/
section

/-!
# Ed448 scalar arithmetic on x86-64: one word

`wordFold` turns the remainder `r < L` in `r8–r14` and the next word `w` in
`rax` into `l + h c` for `2^64 r + w = h 2^446 + l` (`fold_words`), and
`csub` reduces a value below `2L` modulo `L`. Each block is checked against
the numbers it computes, with X448's carry chains, multiply-accumulate steps
and selection.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside stable_reg stable_imm0
  add_chain_ok mulSteps_ok LdStable stores_ok sel_ok stable_scs mask)
open VG.Impl.X448.X86_64 (W w sc stores chain)
open VG.Spec.Ed448 (L)

/-- The remainder: the seven words of `r8–r14`. -/
abbrev rem (s : State) : Nat := rv s W

theorem rem_eq (s : State) : VG.Proof.Ed448.X86_64.rem s = (s.gpr .r8).toNat + 2 ^ 64 * ((s.gpr .r9).toNat + 2 ^ 64 *
    ((s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr .r11).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + 2 ^ 64 *
    ((s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat))))) := by
  simp only [VG.Proof.Ed448.X86_64.rem, rv, W]; omega

theorem rem_split (s : State) : VG.Proof.Ed448.X86_64.rem s = rv s [.r8, .r9, .r10, .r11] +
    2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * rv s [.r12, .r13, .r14] := by
  simp only [VG.Proof.Ed448.X86_64.rem, rv, W]; omega

theorem rotr62 (x : BitVec 64) (h : x.toNat < 2 ^ 62) : (x.rotateRight 62).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt h, Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

theorem shr62 (x : BitVec 64) : (x >>> 62).toNat = x.toNat / 2 ^ 62 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and62 (x : BitVec 64) : (x &&& 0x3fffffffffffffff).toNat = x.toNat % 2 ^ 62 := by
  rw [BitVec.toNat_and, show (0x3fffffffffffffff : BitVec 64).toNat = 2 ^ 62 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `foldPrep`: `h` into `rcx`, `l` into `r8–r14`, `rbp = 0`. -/
theorem foldPrep_ok (s : State) (h6 : (s.gpr .r14).toNat < 2 ^ 62) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .rcx).toNat = (s.gpr .r13).toNat / 2 ^ 62 + 4 * (s.gpr .r14).toNat ∧
      t.gpr .r8 = s.gpr .rax ∧ t.gpr .r9 = s.gpr .r8 ∧ t.gpr .r10 = s.gpr .r9 ∧
      t.gpr .r11 = s.gpr .r10 ∧ t.gpr .r12 = s.gpr .r11 ∧ t.gpr .r13 = s.gpr .r12 ∧
      (t.gpr .r14).toNat = (s.gpr .r13).toNat % 2 ^ 62 ∧ t.gpr .rbp = 0 ∧
      Keeps [.rcx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32,
    execShift, execAlu, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, show 1 ≤ 62 ∧ 62 ≤ 63 by decide, and_self, ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, VG.Proof.Ed448.X86_64.and62 _, rfl, fun r hr => ?_,
    rfl, rfl, rfl⟩
  · have := (s.gpr .r13).isLt
    rw [BitVec.toNat_add, VG.Proof.Ed448.X86_64.shr62, VG.Proof.Ed448.X86_64.rotr62 _ h6, Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2, ite_false]

theorem cWords_val : wv cWords = cL := by decide

theorem ldStable_imm (X : List Reg) (s : State) (v : BitVec 64) :
    LdStable X s (.movImm64 .rax v) v := fun _ _ _ _ _ => rfl

theorem ldStable_cWords (X : List Reg) (s : State) :
    List.Forall₂ (LdStable X s) (cWords.map (.movImm64 .rax ·)) cWords :=
  .cons (VG.Proof.Ed448.X86_64.ldStable_imm _ _ _) <| .cons (VG.Proof.Ed448.X86_64.ldStable_imm _ _ _) <| .cons (VG.Proof.Ed448.X86_64.ldStable_imm _ _ _) <|
    .cons (VG.Proof.Ed448.X86_64.ldStable_imm _ _ _) .nil

/-- `foldMul`: `r8–r14 += rcx · c`, for `rbp = 0` and a sum below `2^448`. -/
theorem foldMul_ok (s : State) (hb : s.gpr .rbp = 0)
    (hlt : VG.Proof.Ed448.X86_64.rem s + (s.gpr .rcx).toNat * cL < 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64) :
    WP isa (.block foldMul) s fun t =>
      VG.Proof.Ed448.X86_64.rem t = VG.Proof.Ed448.X86_64.rem s + (s.gpr .rcx).toNat * cL ∧
      Keeps [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  rw [foldMul, WP.block_append_iff]
  refine WP.mono (mulSteps_ok [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11] s [.r8, .r9, .r10, .r11] _
    cWords s (Keeps.refl _ _) (by decide) (by decide) (by decide) rfl (VG.Proof.Ed448.X86_64.ldStable_cWords _ _))
    fun a ⟨ea, ka⟩ => ?_
  refine WP.mono (add_chain_ok [.r12, .r13, .r14] a .r12 [.r13, .r14] (.reg .rbp) [.imm 0, .imm 0]
    (a.gpr .rbp) [0, 0] (fun _ h => h) (by decide) rfl (stable_reg a (by decide))
    (.cons (stable_imm0 _ _) (.cons (stable_imm0 _ _) .nil))) fun t ⟨c, _, et, kt⟩ => ?_
  refine ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  have g4 : rv t [.r8, .r9, .r10, .r11] = rv a [.r8, .r9, .r10, .r11] :=
    kt.rv_eq (by decide)
  have a3 : rv a [.r12, .r13, .r14] = rv s [.r12, .r13, .r14] := ka.rv_eq (by decide)
  rw [VG.Proof.Ed448.X86_64.cWords_val, hb] at ea
  rw [a3] at et
  have l3 := Proof.X448.X86_64.rv_lt t [.r12, .r13, .r14]
  have hc := Bool.toNat_le c
  simp only [wv, Proof.X448.X86_64.toNat_zero64, List.length_cons, List.length_nil] at ea et l3
  rw [VG.Proof.Ed448.X86_64.rem_split, VG.Proof.Ed448.X86_64.rem_split, g4]
  rw [VG.Proof.Ed448.X86_64.rem_split] at hlt
  generalize rv a [.r8, .r9, .r10, .r11] = A4 at *
  generalize rv s [.r8, .r9, .r10, .r11] = S4 at *
  generalize rv t [.r12, .r13, .r14] = T3 at *
  generalize rv s [.r12, .r13, .r14] = S3 at *
  generalize (s.gpr .rcx).toNat * cL = H at *
  generalize (a.gpr .rbp).toNat = B at *
  generalize c.toNat = C at *
  omega

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- `wordFold`: from the remainder `r < L` and the next word `w` in `rax`, a value
below `2L` congruent to `2^64 r + w`. -/
theorem wordFold_ok (s : State) (hr : VG.Proof.Ed448.X86_64.rem s < L) :
    WP isa (.block wordFold) s fun t => VG.Proof.Ed448.X86_64.rem t < 2 * L ∧
      VG.Proof.Ed448.X86_64.rem t % L = ((s.gpr .rax).toNat + 2 ^ 64 * VG.Proof.Ed448.X86_64.rem s) % L ∧ Keeps VG.Proof.Ed448.X86_64.foldClob s t := by
  have hw := (s.gpr .rax).isLt
  have h0 := (s.gpr .r8).isLt; have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt
  have h3 := (s.gpr .r11).isLt; have h4 := (s.gpr .r12).isLt; have h5 := (s.gpr .r13).isLt
  have h6 := (s.gpr .r14).isLt
  rw [VG.Proof.Ed448.X86_64.rem_eq] at hr
  obtain ⟨h6', hh, hlt, hmod⟩ := fold_words _ _ _ _ _ _ _ _ hw h0 h1 h2 h3 h4 h5 h6 hr
  rw [wordFold, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.foldPrep_ok s h6') fun a ⟨ac, a8, a9, a10, a11, a12, a13, a14, abp, ka⟩ => ?_
  have ra : VG.Proof.Ed448.X86_64.rem a = (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r8).toNat + 2 ^ 64 *
      ((s.gpr .r9).toNat + 2 ^ 64 * ((s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr .r11).toNat +
      2 ^ 64 * ((s.gpr .r12).toNat + 2 ^ 64 * ((s.gpr .r13).toNat % 2 ^ 62)))))) := by
    rw [VG.Proof.Ed448.X86_64.rem_eq, a8, a9, a10, a11, a12, a13, a14]
  have hb : VG.Proof.Ed448.X86_64.rem a + (a.gpr .rcx).toNat * cL <
      2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
    have : 2 * L < 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
      decide +kernel
    rw [ra, ac]; exact Nat.lt_trans hlt this
  refine WP.mono (VG.Proof.Ed448.X86_64.foldMul_ok a abp hb) fun t ⟨et, kt⟩ => ?_
  rw [et, ra, ac]
  refine ⟨hlt, ?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [hmod, VG.Proof.Ed448.X86_64.rem_eq]

theorem kWords_val : wv kWords = 2 ^ 448 - L := by decide +kernel

theorem kWords_lit : kWords = [0xdc873d6d54a7bb0d, 0xde933d8d723a70aa, 0x3bb124b65129c96f,
    0x8335dc16, 0, 0, 0xc000000000000000] := rfl

theorem sbbMask_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .r15 (.reg .r15)]) s fun s' =>
      s'.gpr .r15 = mask c ∧ Keeps [.r15] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq,
    exists_eq_left', BitVec.sub_self]
  refine ⟨by cases c <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The registers `csub` changes. -/
def csubClob : List Reg := [.rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The offsets of `K`'s words but the first. -/
def kOffs : List Nat := [136, 144, 152, 160, 168, 176]

theorem csub_eq : csub = stores TMP W ++ (chain .add .adc W (.mem (sc 128) :: kOffs.map
    fun d => .mem (sc d)) ++ (([.alu .sbb .r15 (.reg .r15)] : List Instr) ++
    (List.range 7).flatMap fun i =>
      [.mov .rax (.mem (sc (TMP + 8 * i))), .alu .xor (w i) (.reg .rax),
        .alu .and (w i) (.reg .r15), .alu .xor (w i) (.reg .rax)])) := rfl

theorem len7 : 64 * [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14].length = 448 := rfl

/-- `csub`: `r8–r14` (below `2L`) modulo `L`, with `K` at `KC`; only `TMP`
is written. -/
theorem csub_ok {s : State} {base : Addr} (hs : Scr s base) (hK : mv s.mem base KC 7 = wv kWords)
    (hx : VG.Proof.Ed448.X86_64.rem s < 2 * L) :
    WP isa (.block csub) s fun t => VG.Proof.Ed448.X86_64.rem t = VG.Proof.Ed448.X86_64.rem s % L ∧
      (∀ r, r ∉ VG.Proof.Ed448.X86_64.csubClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [VG.Proof.Ed448.X86_64.csub_eq, WP.block_append_iff]
  refine WP.mono (stores_ok hs TMP W (by decide)) fun a ⟨va, oa, ga, rda, wra⟩ => ?_
  have hsa : Scr a base := ⟨(ga _).trans hs.rdi, wra ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W a .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 128)) (kOffs.map fun d => .mem (sc d))
    (word a.mem base 128) (kOffs.map fun d => word a.mem base d)
    (fun _ h => h) Proof.X448.X86_64.W_nodup rfl
    (Proof.X448.X86_64.stable_sc hsa (by decide) (by decide))
    (stable_scs hsa (by decide) VG.Proof.Ed448.X86_64.kOffs (by decide))) fun b ⟨c, hc, eb, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.sbbMask_ok b hc) fun d ⟨md, kd⟩ => ?_
  have hsb : Scr b base := hsa.of_keeps kb (by decide)
  have hsd : Scr d base := hsb.of_keeps kd (by decide)
  refine WP.mono (sel_ok hsd (a := TMP) (by decide) md) fun t ⟨wt, kt, mt⟩ => ?_
  have hlt := Proof.X448.X86_64.rv_lt b W
  have hkv : wv (word a.mem base 128 :: kOffs.map fun d => word a.mem base d) = 2 ^ 448 - L := by
    have hmv : mv a.mem base KC 7 = mv s.mem base KC 7 :=
      oa.mv (Or.inl (by decide)) (by simp only [KC]; omega)
    rw [← VG.Proof.Ed448.X86_64.kWords_val, ← hK, ← hmv]
    rfl
  rw [hkv, VG.Proof.Ed448.X86_64.len7, show rv a (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = VG.Proof.Ed448.X86_64.rem a from rfl,
    show VG.Proof.Ed448.X86_64.rem a = VG.Proof.Ed448.X86_64.rem s from Proof.X448.X86_64.rv_congr fun r _ => ga r] at eb
  rw [Proof.X448.X86_64.len_W] at hlt
  have hsel : VG.Proof.Ed448.X86_64.rem t = if c then rv b [.r8, .r9, .r10, .r11, .r12, .r13, .r14] else VG.Proof.Ed448.X86_64.rem s := by
    have mm : d.mem = a.mem := kd.2.1.trans kb.2.1
    cases c with
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      show rv t W = rv s W
      rw [Proof.X448.X86_64.rvW, ← va, Proof.X448.X86_64.W_len, Proof.X448.X86_64.mv7]
      exact Proof.X448.X86_64.val7_congr fun i hi => by
        rw [wt i hi, ite_eq_right Bool.false_ne_true, mm]
    | true =>
      rw [ite_eq_left rfl]
      show rv t W = rv b W
      rw [Proof.X448.X86_64.rvW, Proof.X448.X86_64.rvW]
      exact Proof.X448.X86_64.val7_congr fun i hi => by
        rw [wt i hi, ite_eq_left rfl, kd.1 _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact Proof.X448.X86_64.w_ne_r15 i hi)]
  have h2L : 2 * L ≤ 2 ^ 448 := by decide +kernel
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hsel]
    generalize (2 : Nat) ^ 448 = M at hlt eb h2L
    exact csub_nat h2L hx hlt eb
  · simp only [VG.Proof.Ed448.X86_64.csubClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.1 r (by simp [W, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]), kd.1 r (by simp [hr.2.2.2.2.2.2.2.2]),
      kb.1 r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]), ga r]
  · rw [kt.2.1, kd.2.2.1, kb.2.2.1, rda]
  · rw [kt.2.2, kd.2.2.2, kb.2.2.2, wra]
  · rw [mt, kd.2.1, kb.2.1]; exact oa

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop`. -/
section

/-!
# Ed448 scalar arithmetic on x86-64: the loop over the words

`scalarLoop` consumes the words of an input of `8n + t` bytes from the top,
below the `t` bytes the remainder starts from: the invariant is the value
modulo `L` of the consumed top bytes. The body writes only `TMP`, which the
input does not overlap (it is in another buffer, or elsewhere in the
working space).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs)
open VG.Spec.Ed448 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Ed448.bytesAt m p n).length = n := by
  simp only [VG.Spec.Ed448.bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the bytes above
it. -/
theorem words_step (m : Mem) (p : Addr) (len k : Nat) (hk : 8 * (k + 1) ≤ len) :
    decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (len - 8 * (k + 1))) := by
  have e : len - 8 * k = 8 + (len - 8 * (k + 1)) := by omega
  have hs : VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (len - 8 * (k + 1))) =
      VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (len - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, decodeLE_append, VG.Proof.Ed448.X86_64.bytesAt_length, hw, ha]

def wordRead : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block VG.Proof.Ed448.X86_64.wordRead) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .rax = s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.rbx, .rax] s t := by
  have hn : s.gpr .rbx - (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
      show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [VG.Proof.Ed448.X86_64.wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    State.ea, State.load64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hn, ite_true, ite_false, reduceCtorEq,
    BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl,
    BitVec.add_zero, hr, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h.1, h.2, ite_false], rfl, rfl, rfl⟩

theorem test_zero : ∀ n < 128,
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem test_ok (s : State) (n : Nat) (hn : n < 128) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb,
    VG.Proof.Ed448.X86_64.test_zero n hn]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩

/-- The registers the loop changes. -/
def bodyClob : List Reg := [.rbx, .rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem scalarWord_eq : scalarWord = VG.Proof.Ed448.X86_64.wordRead ++ (wordFold ++ (csub ++
    ([.alu .test .rbx (.reg .rbx)] : List Instr))) := by
  simp only [scalarWord, VG.Proof.Ed448.X86_64.wordRead, List.append_assoc, List.cons_append, List.nil_append]

/-- One word: read, folded in, reduced. -/
theorem scalarWord_ok {s : State} {base : Addr} (hs : Scr s base)
    (hK : mv s.mem base KC 7 = wv kWords) (k : Nat) (hk : 8 * (k + 1) < 128)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hv : VG.Proof.Ed448.X86_64.rem s < L) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧ t.zf = some (decide (k = 0)) ∧
      VG.Proof.Ed448.X86_64.rem t = ((s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * VG.Proof.Ed448.X86_64.rem s) % L ∧
      (∀ r, r ∉ VG.Proof.Ed448.X86_64.bodyClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [VG.Proof.Ed448.X86_64.scalarWord_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : VG.Proof.Ed448.X86_64.rem a = VG.Proof.Ed448.X86_64.rem s := ka.rv_eq (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.wordFold_ok a (by rw [av]; exact hv)) fun b ⟨b2, bm, kb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  have mb : b.mem = s.mem := kb.2.1.trans ka.2.1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.csub_ok hsb (by rw [mb]; exact hK) b2) fun c ⟨cv, gc, rdc, wrc, oc⟩ => ?_
  have hbc : c.gpr .rbx = BitVec.ofNat 64 (8 * k) := by
    rw [gc _ (by decide), kb.1 _ (by decide)]; exact ab
  refine WP.mono (VG.Proof.Ed448.X86_64.test_ok c (8 * k) (by omega) hbc) fun t ⟨tz, tg, tm, trd, twr⟩ => ?_
  refine ⟨(tg _).trans hbc, by rw [tz]; simp; omega, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [show VG.Proof.Ed448.X86_64.rem t = VG.Proof.Ed448.X86_64.rem c from Proof.X448.X86_64.rv_congr fun r _ => tg r, cv, bm, ax, av]
  · simp only [VG.Proof.Ed448.X86_64.bodyClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [tg, gc r (by simp [VG.Proof.Ed448.X86_64.csubClob, hr.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2]),
      kb.1 r (by simp [VG.Proof.Ed448.X86_64.foldClob, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.1]),
      ka.1 r (by simp [hr.1, hr.2.1])]
  · rw [trd, rdc, kb.2.2.1, ka.2.2.1]
  · rw [twr, wrc, kb.2.2.2, ka.2.2.2]
  · rw [tm, ← mb]; exact oc

/-- The loop's invariant, after `n` words are left: the remainder is that of
the bytes from word `n` up, of the `len` bytes at `p`. -/
structure LoopInv (base p : Addr) (len : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  bound : 8 * n ≤ len
  counter : s.gpr .rbx = BitVec.ofNat 64 (8 * n)
  value : VG.Proof.Ed448.X86_64.rem s = decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (p + BitVec.ofNat 64 (8 * n)) (len - 8 * n)) % L
  gpr : ∀ r, r ∉ VG.Proof.Ed448.X86_64.bodyClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base TMP 56 s₀.mem s.mem

theorem readW_outside {base p : Addr} {m m' : Mem} (h : Outside base TMP 56 m m')
    (hp : ∀ i < 8, ofs base (p + BitVec.ofNat 64 i) < TMP ∨
      TMP + 56 ≤ ofs base (p + BitVec.ofNat 64 i)) : m'.readW p 64 = m.readW p 64 :=
  (Mem.readW_congr fun i hi => (h _ (hp i hi)).symm).symm

/-- The loop, from `n₀` words left (`n₀ ≥ 1`), with the remainder of the
bytes above them: the remainder of all `len` bytes. The input's bytes are
outside `TMP`, and readable. -/
theorem scalarLoop_ok {s₀ : State} {base : Addr} (hs : Scr s₀ base)
    (hK : mv s₀.mem base KC 7 = wv kWords) {len n₀ : Nat} (hn : 0 < n₀) (hlen : len < 128)
    (hi : VG.Proof.Ed448.X86_64.LoopInv base (s₀.gpr .rsi) len s₀ n₀ s₀)
    (hr : ∀ k < n₀, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hin : ∀ i < len, ofs base (s₀.gpr .rsi + BitVec.ofNat 64 i) < TMP ∨
      TMP + 56 ≤ ofs base (s₀.gpr .rsi + BitVec.ofNat 64 i)) :
    WP isa scalarLoop s₀ fun t =>
      VG.Proof.Ed448.X86_64.rem t = decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (s₀.gpr .rsi) len) % L ∧
      (∀ r, r ∉ VG.Proof.Ed448.X86_64.bodyClob → t.gpr r = s₀.gpr r) ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      Outside base TMP 56 s₀.mem t.mem := by
  apply WP.loop (fun n s => 0 < n ∧ n ≤ n₀ ∧ VG.Proof.Ed448.X86_64.LoopInv base (s₀.gpr .rsi) len s₀ n s) (n := n₀)
  · intro n s ⟨hn, hnn, hi⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hp : s.gpr .rsi = s₀.gpr .rsi := hi.gpr .rsi (by decide)
    have hss : Scr s base := ⟨(hi.gpr .rdi (by decide)).trans hs.rdi, hi.wr ▸ hs.wr, hs.nowrap⟩
    have hKs : mv s.mem base KC 7 = wv kWords := by
      rw [← hK]; exact hi.mem.mv (Or.inl (by decide)) (by simp only [KC]; omega)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.rd, hi.wr, hp]; exact hr k (by omega)
    have hb := hi.bound
    have hv : VG.Proof.Ed448.X86_64.rem s < L := by rw [hi.value]; exact Nat.mod_lt _ L_pos
    refine WP.mono (VG.Proof.Ed448.X86_64.scalarWord_ok hss hKs k (by omega) hi.counter hread hv)
      fun t ⟨tb, tz, tv, tg, trd, twr, tm⟩ => ?_
    have hw : s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 =
        s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 :=
      VG.Proof.Ed448.X86_64.readW_outside hi.mem fun i hi' => by
        rw [Offset.add_add]; exact hin (8 * k + i) (by omega)
    have vt : VG.Proof.Ed448.X86_64.rem t =
        decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) % L := by
      rw [tv, hp, hw, hi.value, VG.Proof.Ed448.X86_64.words_step _ _ len k hb, Nat.mul_comm (2 ^ 64), Nat.add_comm,
        mod_step]
    have it : VG.Proof.Ed448.X86_64.LoopInv base (s₀.gpr .rsi) len s₀ k t :=
      ⟨by omega, tb, vt, fun r hr => (tg r hr).trans (hi.gpr r hr), trd.trans hi.rd,
        twr.trans hi.wr, hi.mem.trans tm⟩
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], ?_,
        it.gpr, it.rd, it.wr, it.mem⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, by omega, by omega, it⟩
  · exact ⟨hn, Nat.le_refl _, hi⟩

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO`. -/
section

/-!
# Ed448 scalar arithmetic on x86-64: entry and exit

Saving the callee-saved registers, storing `K`, the remainders the loops
start from (the top bytes of an input), and the result: seven words and a
zero byte at the output's address, then the registers restored.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc ea_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `saveAt b`: the callee-saved registers at `[b]`. -/
theorem saveAt_ok (b : Reg) {s : State} {base : Addr} (hc : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveAt b)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  refine WP.mono (Spill.save_ok b saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := saved_lt p hp; rw [hc]; exact ⟨_, hw, contains_sc (by omega)⟩
  · rw [hm, hc]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ saved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega
  · rw [hm, hc]; exact Spill.saveMem_saved _ _ _ _ (by decide)

theorem loadK_ok (s : State) :
    WP isa (.block loadK) s fun t => VG.Proof.Ed448.X86_64.rem t = wv kWords ∧ Keeps W s t := by
  apply WP.of_runBlock
  simp only [loadK, W, kWords, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.Ed448.X86_64.rem, rv, W, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-- `storeK`: `K` at `KC`. -/
theorem storeK_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block storeK) s fun t =>
      mv t.mem base KC 7 = wv kWords ∧ Outside base KC 56 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [storeK, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadK_ok s) fun a ⟨va, ka⟩ => ?_
  refine WP.mono (Proof.X448.X86_64.stores_ok (hs.of_keeps ka (by decide)) KC W (by decide))
    fun t ⟨vt, ot, gt, rdt, wrt⟩ => ⟨by rw [Proof.X448.X86_64.W_len] at vt; rw [vt]; exact va,
      by rw [ka.2.1] at ot; exact ot, fun r hr => (gt r).trans (ka.1 r hr), rdt.trans ka.2.2.1,
      wrt.trans ka.2.2.2⟩

/-! ## The remainders the loops start from -/

theorem load8_ok {s : State} {p : Addr} (hr : InRegions (s.rd ++ s.wr) p 1) :
    s.load8 p = some (s.mem p) := by
  simp only [State.load8, hr, ite_true]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem rotr56 (x : BitVec 64) (h : x.toNat < 2 ^ 8) : (x.rotateRight 56).toNat = 256 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_byte (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The remainder of the top byte of a 57-byte input. -/
theorem init57_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 56) 1) :
    WP isa (.block init57) s fun t =>
      VG.Proof.Ed448.X86_64.rem t = decodeLE (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 56) 1) ∧
      t.gpr .rbx = BitVec.ofNat 64 56 ∧ Keeps (.rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [init57, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32, VG.Proof.Ed448.X86_64.ea_at, VG.Proof.Ed448.X86_64.load8_ok hr,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.Ed448.X86_64.rem, rv, W, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, bytesAt,
      List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, decodeLE,
      BitVec.add_zero, VG.Proof.Ed448.X86_64.toNat_byte]
    rfl
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem decode_two (m : Mem) (p : Addr) :
    decodeLE (bytesAt m p 2) = (m p).toNat + 256 * (m (p + 1)).toNat := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, decodeLE, BitVec.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The remainder of the top two bytes of a 114-byte input. -/
theorem init114_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 112) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 113) 1) :
    WP isa (.block init114) s fun t => VG.Proof.Ed448.X86_64.rem t = decodeLE (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 112) 2) ∧
        t.gpr .rbx = BitVec.ofNat 64 112 ∧ Keeps (.rax :: .rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [init114, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execShift, execAlu,
    State.setReg32, VG.Proof.Ed448.X86_64.ea_at, State.load8, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, h0,
    h1, show 1 ≤ 56 ∧ 56 ≤ 63 by decide, and_self,
    ite_true, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [VG.Proof.Ed448.X86_64.decode_two, show s.gpr .rsi + BitVec.ofNat 64 112 + 1 = s.gpr .rsi + BitVec.ofNat 64 113 by
      rw [BitVec.add_assoc]; rfl]
    simp only [VG.Proof.Ed448.X86_64.rem, rv, W, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
    have b0 := (s.mem (s.gpr .rsi + BitVec.ofNat 64 112)).isLt
    have b1 := (s.mem (s.gpr .rsi + BitVec.ofNat 64 113)).isLt
    rw [BitVec.toNat_add, VG.Proof.Ed448.X86_64.toNat_byte, VG.Proof.Ed448.X86_64.rotr56 _ (by rw [VG.Proof.Ed448.X86_64.toNat_byte]; exact b1), VG.Proof.Ed448.X86_64.toNat_byte]
    simp only [BitVec.toNat_setWidth, Nat.mul_zero, Nat.add_zero]
    have z : (0 : BitVec 32).toNat = 0 := rfl
    omega
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The result -/

/-- Stores relative to a register `b`, as a list. -/
theorem storesR_ok (b : Reg) {q : Addr} {R : Region} :
    ∀ (s : State) (o : Nat) (rs : List Reg), s.gpr b = q → R ∈ s.wr →
      (∀ d, o ≤ d → d + 8 ≤ o + 8 * rs.length → R.Contains (off q d) 8) →
      o + 8 * rs.length < 2 ^ 64 →
      WP isa (.block (Proof.X448.X86_64.storesR b o rs)) s fun s' =>
        mv s'.mem q o rs.length = rv s rs ∧ Outside q o (8 * rs.length) s.mem s'.mem ∧
        Frame [R] s.mem s'.mem ∧ (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | s, _, [], _, _, _, _ =>
    WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Frame.refl _ _, fun _ => rfl, rfl, rfl⟩
  | s, o, r :: rs, hq, hR, hc, hn => by
    rw [Proof.X448.X86_64.storesR, WP.block_cons_iff]
    let s1 : State := { s with mem := s.mem.writeW (off q o) (s.gpr r) }
    have hw : InRegions s.wr (off q o) 8 := ⟨R, hR, hc o (Nat.le_refl _) (by simp; omega)⟩
    refine ⟨s1, by simp only [exec, VG.Proof.Ed448.X86_64.ea_at, hq, State.store64, hw, ite_true]; rfl, ?_⟩
    refine WP.mono (VG.Proof.Ed448.X86_64.storesR_ok b s1 (o + 8) rs hq hR (fun d h₁ h₂ => hc d (by omega)
      (by simp; omega)) (by simp at hn; omega)) fun s' ⟨hv, ho', hf, hg, hrd, hwr⟩ => ?_
    have o1 : Outside q o 8 s.mem s1.mem := writeW_outside _ _ _ (by simp at hn; omega)
    refine ⟨?_, (o1.mono (by omega) (by simp; omega)).trans (ho'.mono (by omega) (by simp; omega)),
      ?_, fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, mv, hv, rv, ho'.word (by omega) (by simp at hn; omega)]
      simp only [s1, word_writeW_self]
      rw [Proof.X448.X86_64.rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self R) _
        (hc o (Nat.le_refl _) (by simp; omega))).trans hf

theorem finish_eq : finish = ([.mov .rax (.mem (sc OUT))] : List Instr) ++
    (Proof.X448.X86_64.storesR .rax 0 W ++ (([.mov32 .rcx (.imm 0), .store8 (at_ .rax 56) .rcx] :
      List Instr) ++ Impl.X448.X86_64.restore)) := by
  simp only [finish, List.append_assoc]; rfl

theorem loadOut_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov .rax (.mem (sc OUT))] : List Instr)) s fun t =>
      t.gpr .rax = word s.mem base OUT ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.X448.X86_64.readSrc_sc hs (show OUT + 8 ≤ 8192 by decide), Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem zeroByte_ok (s : State) {q : Addr} (hq : s.gpr .rax = q)
    (hw : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.mov32 .rcx (.imm 0), .store8 (at_ .rax 56) .rcx] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (q + BitVec.ofNat 64 56) (0 : Byte) ∧
      (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32, VG.Proof.Ed448.X86_64.ea_at,
    State.store8, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hq, hw, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, trivial⟩
  simp only [hr, ite_false]

theorem leBytes_57 {x : Nat} (hx : x < L) :
    Proof.X25519.leBytes 57 x = Proof.X25519.leBytes 56 x ++ [0] := by
  have h : x / 256 ^ 56 = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (by decide +kernel))
  rw [show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, h]
  rfl

/-- A word of the working space, after writes to a region disjoint from it. -/
theorem word_frame {base : Addr} {m m' : Mem} {R : Region} (hF : Frame [R] m m')
    (hd : R.Disjoint ⟨base, 8192⟩) {d : Nat} (hd8 : d + 8 ≤ 8192) :
    word m' base d = word m base d := by
  refine (Mem.readW_congr fun i hi => (hF _ fun r hr hc => ?_).symm).symm
  rw [List.mem_singleton.mp hr] at hc
  refine hd _ hc ?_
  rw [Offset.add_add]
  exact Offset.contains_base base (d := d + i) (n := 1) (by omega) (by omega)

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  rw [show 57 = 56 + 1 from rfl, bytesAt_eq, Proof.X25519.bytesAt_add]
  simp only [bytesAt, Spec.X25519.bytesAt, List.range_one, List.map_cons, List.map_nil,
    BitVec.add_zero]

/-- `finish`: the remainder (below `L`) to the 57 bytes at the output's
address `q`, saved at `OUT`, and the callee-saved registers restored. -/
theorem finish_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : word s.mem base OUT = q)
    (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 64} (hsv : Saved base g s.mem) (hlt : VG.Proof.Ed448.X86_64.rem s < L) :
    WP isa (.block finish) s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (VG.Proof.Ed448.X86_64.rem s) ∧ (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] → t.gpr r = s.gpr r) ∧
      Frame [⟨q, 57⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [VG.Proof.Ed448.X86_64.finish_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadOut_ok hs) fun a ⟨ra, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hc8 : ∀ d, 0 ≤ d → d + 8 ≤ 0 + 8 * W.length → (⟨q, 57⟩ : Region).Contains (off q d) 8 :=
    fun d _ hd' => by
      rw [Proof.X448.X86_64.W_len] at hd'; exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (VG.Proof.Ed448.X86_64.storesR_ok .rax (R := ⟨q, 57⟩) a 0 W (ra.trans hq) (ka.2.2.2 ▸ hwo) hc8
    (by decide)) fun b ⟨vb, ob, fb, gb, rdb, wrb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.zeroByte_ok b (q := q) ((gb _).trans (ra.trans hq))
    ⟨_, by rw [wrb, ka.2.2.2]; exact hwo, Offset.contains_base _ (by omega) (by omega)⟩)
    fun c ⟨mc, gc, rdc, wrc⟩ => ?_
  have fc : Frame [⟨q, 57⟩] s.mem c.mem := by
    rw [mc, ← ka.2.1]
    exact fb.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hsc : Scr c base :=
    ⟨by rw [gc _ (by decide), gb, ka.1 _ (by decide)]; exact hs.rdi,
      by rw [wrc, wrb, ka.2.2.2]; exact hs.wr, hs.nowrap⟩
  have svc : Saved base g c.mem := fun rd hrd => by
    have := saved_lt rd hrd
    rw [← hsv rd hrd]
    exact VG.Proof.Ed448.X86_64.word_frame fc hd (by omega)
  refine WP.mono (Proof.X448.X86_64.restore_ok hsc svc) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨?_, rt, fun r hr => ?_, by rw [mt]; exact fc, by rw [rdt, rdc, rdb, ka.2.2.1], by rw [wrt, wrc, wrb, ka.2.2.2]⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2]), gc r hr.2.1, gb, ka.1 r (by simp [hr.1])]
  rw [mt, VG.Proof.Ed448.X86_64.bytesAt_57, mc, encodeLE_eq, VG.Proof.Ed448.X86_64.leBytes_57 hlt]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · have e : bytesAt (b.mem.writeW (q + BitVec.ofNat 64 56) (0 : Byte)) q 56 = bytesAt b.mem q 56 := by
      simp only [bytesAt]
      refine List.map_congr_left fun i hi => ?_
      simp only [List.mem_range] at hi
      simp only [Mem.writeW]
      apply Mem.write_apply
      rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]
    change Spec.X448.bytesAt b.mem q 56 = _
    rw [Proof.X448.X86_64.bytesAt_mv]
    rw [Proof.X448.X86_64.W_len] at vb
    rw [vb, ka.rv_eq (by decide)]
  · simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
    rfl

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain`. -/
section

/-!
# Ed448 scalar reduction on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarReduceContract` it uses, stated for x86-64), and the
correctness of `vg_ed448_scalar_reduce` against it: every write is in the
working space but the result's, so the input is read unchanged, the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_reduce(out = rdi, wide = rsi, scratch = rdx)`. -/
def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 114⟩] ∧ s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 114⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .rsi) 114)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n)
    (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem Outside.frame {base : Addr} {m m' : Mem} (h : Outside base 0 8192 m m') :
    Frame [⟨base, 8192⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 8192 ≤ (x - base).toNat; omega))

/-- The output's address at `OUT` of the working space `[b]`, and `b` into `rdi`. -/
theorem stash_ok {s : State} {base : Addr} (b : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block [.store (at_ b OUT) .rdi, .mov .rdi (.reg b)]) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .rdi) ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, VG.Proof.Ed448.X86_64.ea_at, hb, State.store64, w,
    ite_true, RegUpd.gpr_setReg_self, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl⟩

theorem scalarReduce_correct {s : State} (hp : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => gprPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rdx = b := ⟨_, rfl⟩
  rw [hbase] at hd hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.saveAt_ok .rdx hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.stash_ok (base := base) .rdx (by rw [g₁]; exact hbase)
    (by rw [wr₁]; exact hws)) fun s₂ ⟨m₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.storeK_ok hs₂) fun s₃ ⟨k₃, o₃, g₃, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  have rsi₃ : s₃.gpr .rsi = s.gpr .rsi := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁]
  have rw₃ : s₃.rd = s.rd ∧ s₃.wr = s.wr := ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  have o₂ : Outside base OUT 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by decide)
  -- The input, readable and outside the working space.
  have hin : ∀ i < 114, InRegions (s₃.rd ++ s₃.wr) (s.gpr .rsi + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨⟨s.gpr .rsi, 114⟩, by rw [rw₃.1, hr]; simp,
      Offset.contains_base _ (d := i) (n := 1) (k := 114) (by omega) (by omega)⟩
  have hfar : ∀ i < 114, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.Ed448.X86_64.far hd hi (by decide)
  have O₃ : Outside base 0 8192 s.mem s₃.mem :=
    (o₁.mono (by decide) (by decide)).trans ((o₂.mono (by decide) (by decide)).trans
      (o₃.mono (by decide) (by decide)))
  have hmem₃ : bytesAt s₃.mem (s.gpr .rsi) 114 = bytesAt s.mem (s.gpr .rsi) 114 := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => O₃ _ (Or.inr (hfar i (List.mem_range.mp hi)))
  apply WP.seq
  rw [reduce114]
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.init114_ok s₃ (by rw [rsi₃]; exact hin 112 (by decide))
    (by rw [rsi₃]; exact hin 113 (by decide))) fun s₄ ⟨v₄, b₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base := hs₃.of_keeps k₄ (by decide)
  have rsi₄ : s₄.gpr .rsi = s.gpr .rsi := (k₄.1 _ (by decide)).trans rsi₃
  have hK₄ : mv s₄.mem base KC 7 = wv kWords := by rw [k₄.2.1]; exact k₃
  have v₄' : VG.Proof.Ed448.X86_64.rem s₄ = decodeLE (bytesAt s₄.mem (s₄.gpr .rsi + BitVec.ofNat 64 (8 * 14))
      (114 - 8 * 14)) % L := by
    rw [v₄, k₄.2.1, rsi₄, rsi₃]
    refine (Nat.mod_eq_of_lt ?_).symm
    rw [VG.Proof.Ed448.X86_64.decode_two]
    have := (s₃.mem (s.gpr .rsi + BitVec.ofNat 64 112)).isLt
    have := (s₃.mem (s.gpr .rsi + BitVec.ofNat 64 112 + 1)).isLt
    have : 65536 < L := by decide +kernel
    omega
  refine WP.mono (VG.Proof.Ed448.X86_64.scalarLoop_ok hs₄ hK₄ (len := 114) (n₀ := 14) (by decide) (by decide)
    ⟨by decide, b₄, v₄', fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₄, k₄.2.2.1, k₄.2.2.2]
      exact ⟨⟨s.gpr .rsi, 114⟩, by rw [rw₃.1, hr]; simp,
        Offset.contains_base _ (d := 8 * k) (n := 8) (k := 114) (by omega) (by omega)⟩)
    (fun i hi => Or.inr (by rw [rsi₄]; have := hfar i hi; simp only [TMP]; omega)))
    fun s₅ ⟨v₅, g₅, rd₅, wr₅, o₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  have hout₅ : word s₅.mem base OUT = s.gpr .rdi := by
    rw [o₅.word (by decide) (by decide), k₄.2.1, o₃.word (by decide) (by decide), m₂,
      word_writeW_self, g₁]
  have sv₅ : Saved base s.gpr s₅.mem := by
    have sv₃ := (sv₁.outside o₂ (by decide)).outside o₃ (by decide)
    have sv₄ : Saved base s.gpr s₄.mem := by rw [k₄.2.1]; exact sv₃
    exact sv₄.outside o₅ (by decide)
  have hlt₅ : VG.Proof.Ed448.X86_64.rem s₅ < L := by rw [v₅]; exact Nat.mod_lt _ L_pos
  refine WP.mono (VG.Proof.Ed448.X86_64.finish_ok hs₅ hout₅ (by rw [wr₅, k₄.2.2.2, rw₃.2]; exact hwo) hos sv₅ hlt₅)
    fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O₅ : Outside base 0 8192 s.mem s₅.mem := by
    have O₄ : Outside base 0 8192 s.mem s₄.mem := by rw [k₄.2.1]; exact O₃
    exact O₄.trans (o₅.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₅ _ (by decide), k₄.1 _ (by decide), g₃ _ (by decide),
        g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((Outside.frame O₅).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    rw [bt, v₅, Spec.Ed448.scalarReduce, rsi₄, k₄.2.1, ← hmem₃]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the encoding

`encode`: with `1/Z` in slot 21, `x = X/Z` and `y = Y/Z` (slots 3 and 4)
fully reduced; the seven words of `y` and a byte holding the low bit of `x`
as its top bit are the 57 bytes at the output's address (RFC 8032 §5.2.2);
then the callee-saved registers are restored.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep Keeps FieldOk rv mv wv word off Outside ofs Saved
  saved_lt mulE freeze_ok W_len rvW val7 mv7 fe)
open VG.Proof.X448 (toFe)
open VG.Impl.X448.X86_64 (W w sc at_ slot freeze)
open VG.Spec.Ed448 (L bytesAt)

theorem rotr57 (x : BitVec 64) (h : x.toNat < 2) : (x.rotateRight 57).toNat = 128 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `rsi = 128 · (r8 mod 2)`. -/
theorem signBit_ok (s : State) :
    WP isa (.block signBit) s fun t =>
      (t.gpr .rsi).toNat = 128 * ((s.gpr .r8).toNat % 2) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have h1 : ((s.gpr .r8) &&& BitVec.signExtend 64 (1 : BitVec 32)).toNat = (s.gpr .r8).toNat % 2 := by
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  apply WP.of_runBlock
  simp only [signBit, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.wr_setFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.rd_setFlags,
    show 1 ≤ 57 ∧ 57 ≤ 63 by decide, and_self, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, fun r hr => by simp only [hr, ite_false], trivial⟩
  rw [VG.Proof.Ed448.X86_64.rotr57 _ (by rw [h1]; omega), h1]

/-- The byte `rsi` at `q + 56`, for `rax = q`. -/
theorem byte56_ok {s : State} {q : Addr} (hq : s.gpr .rax = q)
    (hw : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.store8 (at_ .rax 56) .rsi] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (q + BitVec.ofNat 64 56) ((s.gpr .rsi).setWidth 8) ∧ t.gpr = s.gpr ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed448.X86_64.ea_at, State.store8, hq, hw,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem rv_mod2 (s : State) : rv s W % 2 = (s.gpr .r8).toNat % 2 := by
  simp only [rv, W]; omega

theorem toFe_val' (x : Nat) : (toFe x).val = x % Spec.X448.P := rfl

theorem bytes56_write {m : Mem} {q : Addr} (v : Byte) :
    bytesAt (m.writeW (q + BitVec.ofNat 64 56) v) q 56 = bytesAt m q 56 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem byte56_write (m : Mem) (q : Addr) (v : Byte) :
    (m.writeW (q + BitVec.ofNat 64 56) v) (q + BitVec.ofNat 64 56) = v := by
  simp [Mem.writeW, Mem.write]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
/-- `encode`: the 57 bytes at `q` are the encoding of `y = Y/Z` and the low
bit of `x = X/Z`, for `1/Z` in slot 21. -/
theorem encode_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : word s.mem base OUT = q)
    (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block (encode fld)) s fun t =>
      bytesAt t.mem q 57 = Proof.X25519.leBytes 56 (VG.Proof.X448.X86_64.E s.mem base 1 * VG.Proof.X448.X86_64.E s.mem base 21).val ++
        [BitVec.ofNat 8 (128 * ((VG.Proof.X448.X86_64.E s.mem base 0 * VG.Proof.X448.X86_64.E s.mem base 21).val % 2))] ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: .rsi :: Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧
      Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [encode, WP.block_append_iff]
  refine WP.mono (mulE hf hs 3 0 21) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs1 4 1 21) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs2 (a := slot 3) (by decide)) fun s3 ⟨v3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.signBit_ok s3) fun s4 ⟨r4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 (a := slot 4) (by decide)) fun s5 ⟨v5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have q5 : word s5.mem base OUT = q := by
    rw [k5.2.1, m4, k3.2.1, k2.mem.word (by decide) (by decide), k1.mem.word (by decide) (by decide),
      hq]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadOut_ok hs5) fun s6 ⟨r6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have hc8 : ∀ d, 0 ≤ d → d + 8 ≤ 0 + 8 * W.length → (⟨q, 57⟩ : Region).Contains (off q d) 8 :=
    fun d _ hd' => by
      rw [W_len] at hd'; exact Offset.contains_base _ (by omega) (by omega)
  have wr6 : s6.wr = s.wr := by rw [k6.2.2.2, k5.2.2.2, wr4, k3.2.2.2, k2.wr, k1.wr]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.storesR_ok .rax (R := ⟨q, 57⟩) s6 0 W (r6.trans q5) (by rw [wr6]; exact hwo) hc8
    (by decide)) fun s7 ⟨v7, _, f7, g7, rd7, wr7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.byte56_ok ((g7 _).trans (r6.trans q5)) ⟨_, by rw [wr7, wr6]; exact hwo,
    Offset.contains_base _ (by omega) (by omega)⟩) fun s8 ⟨m8, g8, rd8, wr8⟩ => ?_
  have O6 : Outside base 0 8192 s.mem s6.mem := by
    rw [k6.2.1, k5.2.1, m4, k3.2.1]; exact (k1.mem.trans k2.mem).mono (by decide) (by decide)
  have f8 : Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem s8.mem := by
    rw [m8]
    exact (((VG.Proof.Ed448.X86_64.Outside.frame O6).mono (by simp)).trans (f7.mono (by simp))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains_base q (d := 56) (n := 8 / 8) (k := 57) (by decide) (by decide))
  have sv2 : Saved base g s2.mem := hsv.outside (k1.mem.trans k2.mem) (by decide)
  have sv6 : Saved base g s6.mem := by rw [k6.2.1, k5.2.1, m4, k3.2.1]; exact sv2
  have sv7 : Saved base g s7.mem := fun rd hrd => by
    have := saved_lt rd hrd; rw [← sv6 rd hrd]; exact VG.Proof.Ed448.X86_64.word_frame f7 hd (by omega)
  have sv8 : Saved base g s8.mem := fun rd hrd => by
    have := saved_lt rd hrd
    rw [← sv7 rd hrd, m8]
    exact VG.Proof.Ed448.X86_64.word_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 56) (n := 8 / 8) (k := 57) (by decide) (by decide))) hd (by omega)
  have hs8 : Scr s8 base := ⟨by rw [g8, g7]; exact hs6.rdi, wr8 ▸ wr7 ▸ hs6.wr, hs6.nowrap⟩
  refine WP.mono (Proof.X448.X86_64.restore_ok hs8 sv8) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨?_, rt, fun r hr => ?_, by rw [mt]; exact f8, by rw [rdt, rd8, rd7, k6.2.2.1, k5.2.2.1,
    rd4, k3.2.2.1, k2.rd, k1.rd], by rw [wrt, wr8, wr7, wr6]⟩
  · -- The bytes.
    have e4 : VG.Proof.X448.X86_64.E s2.mem base 4 = VG.Proof.X448.X86_64.E s.mem base 1 * VG.Proof.X448.X86_64.E s.mem base 21 := by
      rw [e2, e1]; rfl
    have e3 : VG.Proof.X448.X86_64.E s2.mem base 3 = VG.Proof.X448.X86_64.E s.mem base 0 * VG.Proof.X448.X86_64.E s.mem base 21 := by
      rw [e2, e1]; rfl
    have x3 : rv s3 W = (VG.Proof.X448.X86_64.E s.mem base 0 * VG.Proof.X448.X86_64.E s.mem base 21).val := by
      rw [v3, ← e3]; rfl
    have y5 : rv s5 W = (VG.Proof.X448.X86_64.E s.mem base 1 * VG.Proof.X448.X86_64.E s.mem base 21).val := by
      rw [v5, m4, k3.2.1, ← e4]; rfl
    have b7 : bytesAt s7.mem q 56 = Proof.X25519.leBytes 56 (rv s5 W) := by
      have h := Proof.X448.X86_64.bytesAt_mv s7.mem q
      rw [W_len] at v7
      rw [v7, Proof.X448.X86_64.Keeps.rv_eq k6 (by decide)] at h
      exact h
    have rsi7 : s7.gpr .rsi = s4.gpr .rsi := by
      rw [g7, k6.1 _ (by decide), k5.1 _ (by decide)]
    have sb : (s7.gpr .rsi).setWidth 8 =
        BitVec.ofNat 8 (128 * ((VG.Proof.X448.X86_64.E s.mem base 0 * VG.Proof.X448.X86_64.E s.mem base 21).val % 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, rsi7, r4, BitVec.toNat_ofNat, ← VG.Proof.Ed448.X86_64.rv_mod2, x3]
    rw [mt, VG.Proof.Ed448.X86_64.bytesAt_57, m8, VG.Proof.Ed448.X86_64.bytes56_write, VG.Proof.Ed448.X86_64.byte56_write, b7, y5, sb]
  · have s1 : ∀ x ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by decide
    have s3 : ∀ x ∈ Reg.rax :: Reg.r15 :: W, x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by
      decide
    have s4 : ∀ x ∈ [Reg.rax], x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by decide
    have hr' : r ∉ Proof.X448.X86_64.clob := fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hsi : r ≠ .rsi := fun h => hr (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [gt r (fun h => hr (s1 r h)), g8, g7, k6.1 r (fun h => hr (s4 r h)),
      k5.1 r (fun h => hr (s3 r h)), g4 r hsi, k3.1 r (fun h => hr (s3 r h)), k2.gpr r hr',
      k1.gpr r hr']

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseLit`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86_64.scalarBase

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the contract the proof is written against

The facts of `Spec.Ed448.scalarBaseContract` the proof uses, stated for
x86-64, in a module of their own: callers proven for any code meeting them
need not import the proof, and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- `vg_ed448_scalar_base(out = rdi, scalar = rsi, scratch = rdx)`. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 57⟩] ∧ s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .rdi) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 57)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseMain`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: the whole function

The correctness of `vg_ed448_scalar_base` against the contract the proof is
written against (`scalarBaseLocal`, `BaseLocal.lean`): the scalar's bits, the
loop (`R` ends as the reference ladder's point, which encodes `[k]B` by
`BaseLadderOk`), the inversion of `Z` and the encoding, every write in the
working space but the result's, so the scalar is read unchanged, the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E FieldOk word off Outside ofs Saved clob writeW_outside
  word_writeW_self invert_ok setRbx_ok E_outside contains_sc ofs_off')
open VG.Impl.X448.X86_64 (BITS slot)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The result's bytes: those of `y = Y/Z` and the sign of `x = X/Z`, for
`(X : Y : Z)` the ladder's point of a scalar of 57 bytes. -/
theorem encode_result (hL : BaseLadderOk) {X Y Z : Spec.X448.Fe} {m : Mem} {p : Addr}
    (h : (⟨X, Y, Z⟩ : Spec.Ed448.Point) = ladder (decodeLE (bytesAt m p 57)) 456) :
    Proof.X25519.leBytes 56 (Y * Proof.X448.invert Z).val ++
      [BitVec.ofNat 8 (128 * ((X * Proof.X448.invert Z).val % 2))] =
      Spec.Ed448.scalarBase (bytesAt m p 57) := by
  rw [Spec.Ed448.scalarBase, ← hL _ (decodeLE_below (by rw [bytesAt_eq]; simp [Spec.X25519.bytesAt])),
    ← h, encodePoint_code]

/-- The output's address into `r15`, the working space into `rdi`. -/
theorem movOut_ok (s : State) :
    WP isa (.block ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rdx)] : List Instr)) s fun t =>
      t.mem = s.mem ∧ t.gpr .r15 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ∉ [Reg.rdi, .r15] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp [RegUpd.gpr_setReg]
  · simp [RegUpd.gpr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem stashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block stashOut) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .r15) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [stashOut, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed448.X86_64.ea_at, hb,
    State.store64, w, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem scalarBase_correct (hL : BaseLadderOk) {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith fld) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rdx = b := ⟨_, rfl⟩
  rw [hbase] at hd hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  -- The entry: the callee-saved registers, the output's address, the constants.
  apply WP.seq
  rw [entry, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.saveAt_ok .rdx hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.movOut_ok s₁) fun s₂ ⟨m₂, r15₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  rw [g₁, hbase] at di₂
  rw [g₁] at r15₂
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.consts_ok hs₂) fun s₃ ⟨p₃, q₃, d₃, o₃, g₃, rd₃, wr₃, _⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  have rsi₃ : s₃.gpr .rsi = s.gpr .rsi := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁]
  have rw₃ : s₃.rd = s.rd ∧ s₃.wr = s.wr := ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  have hfar : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => VG.Proof.Ed448.X86_64.far hd hi (by decide)
  have O₃ : Outside base 0 8192 s.mem s₃.mem := by
    rw [m₂] at o₃
    exact (o₁.mono (by decide) (by decide)).trans (o₃.mono (by decide) (by decide))
  have hmem₃ : ∀ i < 57, s₃.mem (s.gpr .rsi + BitVec.ofNat 64 i) =
      s.mem (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => O₃ _ (Or.inr (hfar i hi))
  -- The scalar's bits.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.bits_ok hs₃ rsi₃ (fun q hq => ⟨⟨s.gpr .rsi, 57⟩, by rw [rw₃.1, hr]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 57) (by omega) (by omega)⟩) hfar)
    fun s₄' ⟨g₄', rd₄', wr₄', o₄', b₄⟩ => ?_
  have hs₄' : Scr s₄' base := ⟨(g₄' _ (by decide)).trans hs₃.rdi, wr₄' ▸ hs₃.wr, hs₃.nowrap⟩
  -- The output's address at `OUT`.
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.stashOut_ok hs₄'.rdi hs₄'.wr) fun s₄ ⟨m₄, g₄'', rd₄'', wr₄''⟩ => ?_
  have g₄ : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s₄.gpr r = s₃.gpr r := fun r hr => by
    rw [g₄'', g₄' r hr]
  have rd₄ : s₄.rd = s₃.rd := by rw [rd₄'', rd₄']
  have wr₄ : s₄.wr = s₃.wr := by rw [wr₄'', wr₄']
  have oo : Outside base OUT 8 s₄'.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by decide)
  have o₄ : Outside base OUT (BITS + 456 - OUT) s₃.mem s₄.mem :=
    (o₄'.mono (by decide) (by decide)).trans (oo.mono (by decide) (by decide))
  have hs₄ : Scr s₄ base := ⟨by rw [g₄'']; exact hs₄'.rdi, wr₄'' ▸ hs₄'.wr, hs₄'.nowrap⟩
  have b₄' : ∀ t < 456, s₄.mem (off base (BITS + t)) =
      BitVec.ofNat 8 (((s₃.mem (s.gpr .rsi + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1) :=
    fun t ht => by
      rw [oo _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, OUT]; omega))]
      exact b₄ t ht
  have hout₄ : word s₄.mem base OUT = s.gpr .rdi := by
    have r15₄ : s₄'.gpr .r15 = s.gpr .rdi := by rw [g₄' _ (by decide), g₃ _ (by decide), r15₂]
    rw [m₄, word_writeW_self, r15₄]
  have e₄ : ∀ i : Index, VG.Proof.X448.X86_64.E s₄.mem base i = VG.Proof.X448.X86_64.E s₃.mem base i := fun i => by
    have h1 := Proof.X448.X86_64.slot_lt i
    have h2 := Proof.X448.X86_64.slot_ge i
    simp only [Impl.X448.X86_64.ACC] at h1
    exact (E_outside oo i (Or.inr (by simp only [OUT]; omega))).trans
      (E_outside o₄' i (Or.inl (by simp only [BITS]; omega)))
  -- The loop.
  apply WP.seq
  rw [mulLoop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 456))]) s₄ _ from
    setRbx_ok s₄ 456 (by decide)) fun s₅ ⟨rbx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  let K := decodeLE (bytesAt s.mem (s.gpr .rsi) 57)
  have hbits : ∀ t < 456, s₅.mem (off base (BITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    intro t ht
    rw [m₅, b₄' t ht, hmem₃ _ (by omega), scalar_bit s.mem _ ht]
  have e₅ : ∀ i : Index, VG.Proof.X448.X86_64.E s₅.mem base i = VG.Proof.X448.X86_64.E s₃.mem base i := fun i => by rw [m₅, e₄]
  have I₅ : VG.Proof.Ed448.X86_64.MInv base K s₅ 456 s₅ := by
    refine ⟨hs₅, rbx₅, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, ?_, ?_⟩
    · show Proof.Ed448.pt (VG.Proof.X448.X86_64.E s₅.mem base) 8 9 10 = _
      simp only [Proof.Ed448.pt, e₅]; exact q₃
    · rw [e₅]; exact d₃
    · simp only [Proof.Ed448.pt, e₅, Nat.sub_self]; exact p₃
  refine WP.mono (VG.Proof.Ed448.X86_64.loop_ok hf hbits 456 s₅ (by decide) (by decide) I₅) fun s₆ I₆ => ?_
  -- The inversion of `Z`.
  apply WP.seq
  refine WP.mono (invert_ok hf I₆.scr) fun s₇ ⟨g₇, rd₇, wr₇, o₇, e₇⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨(g₇ _ (by decide) (by decide)).trans I₆.scr.rdi, wr₇ ▸ I₆.scr.wr, hn⟩
  -- The encoding.
  have hout₇ : word s₇.mem base OUT = s.gpr .rdi := by
    rw [o₇.word (by decide) (by decide), I₆.mem.word (by decide) (by decide), m₅, hout₄]
  have sv₇ : Saved base s.gpr s₇.mem := by
    have sv₂ : Saved base s.gpr s₂.mem := by rw [m₂]; exact sv₁
    have sv₄ := (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
    have sv₅ : Saved base s.gpr s₅.mem := by rw [m₅]; exact sv₄
    exact (sv₅.outside I₆.mem (by decide)).outside o₇ (by decide)
  refine WP.mono (VG.Proof.Ed448.X86_64.encode_ok hf hs₇ hout₇ (by rw [wr₇, I₆.wr, wr₅, wr₄, rw₃.2]; exact hwo) hos sv₇)
    fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O₇ : Outside base 0 8192 s.mem s₇.mem := by
    have O₅ : Outside base 0 8192 s.mem s₅.mem := by
      rw [m₅]; exact O₃.trans (o₄.mono (by decide) (by decide))
    exact (O₅.trans (I₆.mem.mono (by decide) (by decide))).trans (o₇.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₇ _ (by decide) (by decide), I₆.gpr _ (by decide), g₅ _ (by decide),
        g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((VG.Proof.Ed448.X86_64.Outside.frame O₇).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    have r₆ := I₆.rep
    rw [Nat.sub_zero] at r₆
    rw [bt, e₇, E_outside o₇ 0 (by decide), E_outside o₇ 1 (by decide)]
    exact VG.Proof.Ed448.X86_64.encode_result hL r₆

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified`. -/
section

/-!
# Ed448 base-point multiplication on x86-64: `Verified`

Correctness including the ABI, given that the reference ladder encodes `[k]B`
(`BaseLadderOk`, which the registration files pass in), constant time
(by taint tracking: the only branches are on the loop counters, and every
address is an argument plus a constant or a counter), and a concrete state
satisfying the signature's contract.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarBaseSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarBaseτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarBase_agree {s₁ s₂ : State} (h₁ : scalarBaseLocal.pre s₁)
    (h₂ : scalarBaseLocal.pre s₂) (hpub : scalarBaseLocal.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Ed448.X86_64.scalarBaseτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarBaseLocal.pre s → X86_64.Taint.Wf VG.Proof.Ed448.X86_64.scalarBaseτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed448.X86_64.scalarBaseτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Ed448.X86_64.scalarBaseτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Ed448.X86_64.scalarBaseτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarBaseτ] at h
  · intro sl h; simp [VG.Proof.Ed448.X86_64.scalarBaseτ] at h

theorem scalarBase_ok (hL : Proof.Ed448.BaseLadderOk) (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed448.X86_64.scalarBase_correct Proof.X448.X86_64.baseline_ok hL hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := scalarBase) (by lit_decide) he h.1, h.2⟩

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed448.X86_64.scalarBaseτ
    (fun _ _ h₁ h₂ hp => VG.Proof.Ed448.X86_64.scalarBase_agree h₁ h₂ hp) (by taint_decide)

theorem scalarBase_verified (hL : Proof.Ed448.BaseLadderOk) : Verified X86_64.target scalarBase
    (Spec.Ed448.scalarBaseContract X86_64.abi) :=
  Verified.of_correct (VG.Proof.Ed448.X86_64.scalarBase_ok hL) VG.Proof.Ed448.X86_64.scalarBase_ct (by
    sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed448.X86_64.scalarBaseLocal]
      [scalarBaseSat] using VG.Proof.Ed448.X86_64.scalarBaseSat)

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot`. -/
section

/-!
# Ed448 verification's equation on x86-64: the square root's power

`root fld 12` writes only the temporaries of X448's inversion (slots 14–21)
and the product's words, and the counter `rbx` (an `ISpec`, as X448's
inversion); slot 21 ends as `rootPow` of slot 12.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Env ISpec IKeep FieldOk Scr E Outside clob opMul opSqn sqnI mulI)

/-- The slots after `root`. -/
def rootEnv (e : Env) : Env :=
  opMul 21 21 20 (opSqn 21 21 223 (opMul 21 21 12 (opSqn 21 20 1
    (opMul 20 20 14 (opSqn 20 20 2 (opMul 20 20 15 (opSqn 20 20 4 (opMul 20 20 16 (opSqn 20 20 8
    (opMul 20 20 17 (opSqn 20 20 16 (opMul 20 20 19 (opSqn 20 20 64 (opMul 20 20 19 (opSqn 20 19 64
    (opMul 19 19 18 (opSqn 19 18 32 (opMul 18 18 17 (opSqn 18 17 16 (opMul 17 17 16 (opSqn 17 16 8
    (opMul 16 16 15 (opSqn 16 15 4 (opMul 15 15 14 (opSqn 15 14 2 (opMul 14 14 12
    (opSqn 14 12 1 e)))))))))))))))))))))))))))

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem root_spec (base : Addr) : ISpec base (root fld 12) VG.Proof.Ed448.X86_64.rootEnv := by
  have h : ISpec base _ _ :=
    (sqnI hf base 14 12 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 14 14 12 (by decide)).seq <|
    (sqnI hf base 15 14 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 15 15 14 (by decide)).seq <|
    (sqnI hf base 16 15 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 16 16 15 (by decide)).seq <|
    (sqnI hf base 17 16 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 17 17 16 (by decide)).seq <|
    (sqnI hf base 18 17 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 18 18 17 (by decide)).seq <|
    (sqnI hf base 19 18 (by decide) 32 (by decide) (by decide)).seq <|
    (mulI hf base 19 19 18 (by decide)).seq <|
    (sqnI hf base 20 19 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 17 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 16 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 15 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 14 (by decide)).seq <|
    (sqnI hf base 21 20 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 21 21 12 (by decide)).seq <|
    (sqnI hf base 21 21 (by decide) 223 (by decide) (by decide)).seq
    (mulI hf base 21 21 20 (by decide))
  exact h

theorem rootEnv_eval (e : Env) : VG.Proof.Ed448.X86_64.rootEnv e 21 = rootPow (e 12) := by
  simp (config := {decide := true}) only [VG.Proof.Ed448.X86_64.rootEnv, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Proof.X448.X86_64.Index) (hi : i.val < 14) : VG.Proof.Ed448.X86_64.rootEnv e i = e i := by
  have h1 : i ≠ 14 := fun h => absurd hi (by rw [h]; decide)
  have h2 : i ≠ 15 := fun h => absurd hi (by rw [h]; decide)
  have h3 : i ≠ 16 := fun h => absurd hi (by rw [h]; decide)
  have h4 : i ≠ 17 := fun h => absurd hi (by rw [h]; decide)
  have h5 : i ≠ 18 := fun h => absurd hi (by rw [h]; decide)
  have h6 : i ≠ 19 := fun h => absurd hi (by rw [h]; decide)
  have h7 : i ≠ 20 := fun h => absurd hi (by rw [h]; decide)
  have h8 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  simp only [VG.Proof.Ed448.X86_64.rootEnv, opMul, opSqn, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks`. -/
section

/-!
# Ed448 verification's equation on x86-64: the checks

Each check ORs into the word `BAD` of the working space a word that is 0
exactly when it passes: the equality of two field elements (`eqSlots_ok`, by
comparing their full reductions word by word), and `S < L` (`sCheck_ok`, by
the carry of `S + 2^448 - L` and its byte 56). `erun` runs a block
symbolically, keeping the register writes folded.
-/

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside ofs writeW_outside word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_)

/-- Runs a block symbolically, keeping the register writes folded. -/
syntax "erun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| erun) => `(tactic| erun [])
  | `(tactic| erun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        readSrc32, execAlu, execShift, State.setReg32, State.load64, State.load8, State.store64,
        State.store8, sc, VG.Proof.Ed448.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.cf_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, RegUpd.zf_arithFlags,
        RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
        RegUpd.cf_setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
        ite_true, ite_false, reduceCtorEq, true_and, and_true, $ls,*]))

theorem orBad_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block orBad) s fun t =>
      t.mem = s.mem.writeW (off base BAD) (word s.mem base BAD ||| s.gpr .rdx) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 BAD) 8 := hs.read (by decide)
  have wb : InRegions s.wr (base + BitVec.ofNat 64 BAD) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [orBad, hs.rdi, rb, wb]
  exact fun r hr => by simp only [hr, ite_false]

theorem isZero_ok (s : State) :
    WP isa (.block isZero) s fun t =>
      t.gpr .rdx = (if s.gpr .rdx = 0 then 1 else 0) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun [isZero]
  refine ⟨?_, fun r hr => by simp only [hr, ite_false]⟩
  rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl]
  by_cases h : s.gpr .rdx = 0
  · rw [h]; decide
  · have h' : ¬ (s.gpr .rdx).toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by
      show _ = 0; omega))
    rw [ite_eq_right h, decide_eq_false h']
    decide

theorem diff7 (f g : Nat → BitVec 64) :
    ((((((((0#64 ||| f 0 ^^^ g 0) ||| f 1 ^^^ g 1) ||| f 2 ^^^ g 2) ||| f 3 ^^^ g 3) |||
      f 4 ^^^ g 4) ||| f 5 ^^^ g 5) ||| f 6 ^^^ g 6) = 0#64) ↔ ∀ i < 7, f i = g i := by
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · intro h i hi
    match i, hi with
    | 0, _ => exact h.1.1.1.1.1.1.2
    | 1, _ => exact h.1.1.1.1.1.2
    | 2, _ => exact h.1.1.1.1.2
    | 3, _ => exact h.1.1.1.2
    | 4, _ => exact h.1.1.2
    | 5, _ => exact h.1.2
    | 6, _ => exact h.2
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨trivial, h 0 (by decide)⟩, h 1 (by decide)⟩, h 2 (by decide)⟩, h 3 (by decide)⟩,
      h 4 (by decide)⟩, h 5 (by decide)⟩, h 6 (by decide)⟩

theorem diffWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 56 ≤ 8192) :
    WP isa (.block (diffWords o)) s fun t =>
      (t.gpr .rdx = 0 ↔ ∀ i < 7, word s.mem base (o + 8 * i) = s.gpr (w i)) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r0 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 0)) 8 := hs.read (by omega)
  have r1 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 1)) 8 := hs.read (by omega)
  have r2 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 2)) 8 := hs.read (by omega)
  have r3 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 3)) 8 := hs.read (by omega)
  have r4 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 4)) 8 := hs.read (by omega)
  have r5 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 5)) 8 := hs.read (by omega)
  have r6 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 6)) 8 := hs.read (by omega)
  erun [diffWords, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, w, W, hs.rdi, r0, r1, r2, r3, r4,
    r5, r6]
  exact ⟨VG.Proof.Ed448.X86_64.diff7 (fun i => word s.mem base (o + 8 * i)) (fun i => s.gpr (W.getD i .r8)),
    fun r h1 h2 => by simp only [h1, h2, ite_false]⟩

open VG.Proof.X448.X86_64 (rv mv fe E Index Keeps freeze_ok stores_ok val7 mv7 rvW slot_lt W_len)

theorem val7_inj {f g : Nat → Nat} (hf : ∀ i < 7, f i < 2 ^ 64) (hg : ∀ i < 7, g i < 2 ^ 64) :
    val7 f = val7 g ↔ ∀ i < 7, f i = g i := by
  constructor
  · intro h
    have d : ∀ {a b c e : Nat}, a < 2 ^ 64 → c < 2 ^ 64 → a + 2 ^ 64 * b = c + 2 ^ 64 * e →
        a = c ∧ b = e := fun ha hc h => by omega
    simp only [val7] at h
    obtain ⟨e0, h⟩ := d (hf 0 (by decide)) (hg 0 (by decide)) h
    obtain ⟨e1, h⟩ := d (hf 1 (by decide)) (hg 1 (by decide)) h
    obtain ⟨e2, h⟩ := d (hf 2 (by decide)) (hg 2 (by decide)) h
    obtain ⟨e3, h⟩ := d (hf 3 (by decide)) (hg 3 (by decide)) h
    obtain ⟨e4, h⟩ := d (hf 4 (by decide)) (hg 4 (by decide)) h
    obtain ⟨e5, e6⟩ := d (hf 5 (by decide)) (hg 5 (by decide)) h
    intro i hi
    match i, hi with
    | 0, _ => exact e0
    | 1, _ => exact e1
    | 2, _ => exact e2
    | 3, _ => exact e3
    | 4, _ => exact e4
    | 5, _ => exact e5
    | 6, _ => exact e6
  · exact fun h => VG.Proof.X448.X86_64.val7_congr h

theorem toFe_eq_iff (x y : Nat) : VG.Proof.X448.toFe x = VG.Proof.X448.toFe y ↔ x % Spec.X448.P = y % Spec.X448.P := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simpa [VG.Proof.X448.toFe_val] using this
  · intro h
    exact Fin.ext (by simpa [VG.Proof.X448.toFe_val] using h)

/-- Checks write only the words `[BAD, CAN + 56)` and the registers `rax`, `rdx`, `r15`, `W`. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ Reg.rax :: Reg.rdx :: Reg.r15 :: W → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base BAD 80 s.mem t.mem

theorem CKeep.trans {base : Addr} {s t u : State} (h₁ : VG.Proof.Ed448.X86_64.CKeep base s t) (h₂ : VG.Proof.Ed448.X86_64.CKeep base t u) :
    VG.Proof.Ed448.X86_64.CKeep base s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86_64.CKeep base s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem E_bad {base : Addr} {m m' : Mem} (h : Outside base BAD 80 m m') : VG.Proof.X448.X86_64.E m' base = VG.Proof.X448.X86_64.E m base := by
  funext i
  have := slot_lt i
  simp only [VG.Impl.X448.X86_64.ACC] at this
  exact VG.Proof.X448.X86_64.E_outside h i (Or.inl (by simp only [BAD]; omega))

theorem CKeep.E {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86_64.CKeep base s t) : VG.Proof.X448.X86_64.E t.mem base = VG.Proof.X448.X86_64.E s.mem base :=
  VG.Proof.Ed448.X86_64.E_bad h.mem

/-- `BAD |= c`, with `c = 0` exactly when slots `a` and `b` are the same field element. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Index) :
    WP isa (.block (eqSlots a.val b.val)) s fun t =>
      ∃ c : BitVec 64, (c = 0 ↔ VG.Proof.X448.X86_64.E s.mem base a = VG.Proof.X448.X86_64.E s.mem base b) ∧
        word t.mem base BAD = word s.mem base BAD ||| c ∧ VG.Proof.Ed448.X86_64.CKeep base s t ∧
        word t.mem base SIGN = word s.mem base SIGN := by
  have ha := slot_lt a; have hb := slot_lt b
  simp only [VG.Impl.X448.X86_64.ACC] at ha hb
  rw [eqSlots, WP.block_append_iff]
  refine WP.mono (freeze_ok hs (a := VG.Impl.X448.X86_64.slot a.val) ha) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs1 CAN W (by rw [W_len]; decide)) fun s2 ⟨v2, o2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs2 (a := VG.Impl.X448.X86_64.slot b.val) hb) fun s3 ⟨v3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.diffWords_ok hs3 (o := CAN) (by decide)) fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide) (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.orBad_ok hs4) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  -- the memory: CAN written, then BAD.
  have O2 : Outside base BAD 80 s.mem s2.mem := by
    rw [← k1.2.1]; exact o2.mono (by decide) (by rw [W_len]; decide)
  have O4 : Outside base BAD 80 s.mem s4.mem := by rw [m4, k3.2.1]; exact O2
  have Ot : Outside base BAD 80 s.mem t.mem := by
    rw [mt]; exact O4.trans ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  -- the slots are unchanged until the stores.
  have e2 : VG.Proof.X448.X86_64.E s2.mem base = VG.Proof.X448.X86_64.E s.mem base := VG.Proof.Ed448.X86_64.E_bad O2
  refine ⟨s4.gpr .rdx, ?_, ?_, ?_, ?_⟩
  · rw [d4]
    have hA : mv s3.mem base CAN 7 = fe s.mem base (VG.Impl.X448.X86_64.slot a.val) % Spec.X448.P := by
      rw [k3.2.1, ← v1]; exact v2
    have hB : rv s3 W = fe s.mem base (VG.Impl.X448.X86_64.slot b.val) % Spec.X448.P := by
      rw [v3]; exact congrArg (· % Spec.X448.P) (O2.mv (Or.inl (by simp only [BAD]; omega)) (by omega))
    have key : (∀ i < 7, word s3.mem base (CAN + 8 * i) = s3.gpr (w i)) ↔
        mv s3.mem base CAN 7 = rv s3 W := by
      rw [mv7, rvW, VG.Proof.Ed448.X86_64.val7_inj (fun i _ => BitVec.isLt _) (fun i _ => BitVec.isLt _)]
      constructor
      · intro h i hi; exact congrArg BitVec.toNat (h i hi)
      · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)
    rw [key, hA, hB, ← VG.Proof.Ed448.X86_64.toFe_eq_iff]
    rfl
  · rw [mt, word_writeW_self, m4, k3.2.1]
    have : word s2.mem base BAD = word s.mem base BAD := by
      rw [o2.word (by left; decide) (by decide), k1.2.1]
    rw [this]
  · refine ⟨fun r hr => ?_, by rw [rdt, rd4, k3.2.2.1, rd2, k1.2.2.1],
      by rw [wrt, wr4, k3.2.2.2, wr2, k1.2.2.2], Ot⟩
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [gt r h1, g4 r h1 h2, k3.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩), g2,
      k1.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩)]
  · rw [mt, (writeW_outside s4.mem base _ (by decide)).word (Or.inr (by decide)) (by decide), m4, k3.2.1,
      o2.word (Or.inl (by decide)) (by decide), k1.2.1]

open VG.Proof.X448.X86_64 (wv add_chain_ok stable_sc stable_scs W_nodup)

/-- The seven words at `p` into `r8–r14`. -/
theorem loadsS_ok (s : State) {p : Addr} (hp : s.gpr .rsi = p)
    (hr : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block ((List.range 7).map fun i => Instr.mov (w i) (.mem (at_ .rsi (8 * i))))) s fun t =>
      rv t W = mv s.mem p 0 7 ∧ Keeps W s t := by
  have r0 := hr 0 (by decide); have r1 := hr 1 (by decide); have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide); have r4 := hr 4 (by decide); have r5 := hr 5 (by decide)
  have r6 := hr 6 (by decide)
  erun [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, w, W, hp, r0, r1, r2, r3, r4, r5, r6, List.getD_cons_succ, List.getD_cons_zero,
    Keeps, Nat.reduceMul, Nat.reduceAdd]
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [rv, mv, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte, VG.Proof.X448.X86_64.word, off,
      Nat.reduceAdd]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  simp only [h1, h2, h3, h4, h5, h6, h7, ite_false]

theorem setWidth8_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this
    exact this
  · rintro rfl; rfl

theorem ofBool_eq_zero (c : Bool) : (BitVec.ofBool c).setWidth 64 = 0 ↔ c = false := by
  cases c <;> decide

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem sTail_ok (s : State) {p : Addr} (hp : s.gpr .rsi = p) {c : Bool} (hc : s.cf = some c)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.mov32 .rdx (.imm 0), .alu .adc .rdx (.imm 0), .movzx8 .rax (at_ .rsi 56),
      .alu .or .rdx (.reg .rax)] : List Instr)) s fun t =>
      (t.gpr .rdx = 0 ↔ c = false ∧ s.mem (p + BitVec.ofNat 64 56) = 0) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun [hp, hr, hc]
  refine ⟨?_, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩
  rw [show BitVec.setWidth 64 (0 : BitVec 32) + BitVec.signExtend 64 (0 : BitVec 32) +
      BitVec.setWidth 64 (BitVec.ofBool c) = BitVec.setWidth 64 (BitVec.ofBool c) by cases c <;> rfl,
    VG.Proof.Ed448.X86_64.or_eq_zero64, VG.Proof.Ed448.X86_64.ofBool_eq_zero, VG.Proof.Ed448.X86_64.setWidth8_eq_zero]

open VG.Proof.X448.X86_64 (Outside2 len_W)

theorem sCheck_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (.block sCheck) s fun t =>
      ∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 57) < Spec.Ed448.L) ∧
        word t.mem base BAD = word s.mem base BAD ||| c ∧
        (∀ r, r ∉ Reg.rax :: Reg.rdx :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        Outside2 base KC 56 BAD 8 s.mem t.mem := by
  rw [sCheck, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.storeK_ok hs) fun s1 ⟨k1, o1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  have hb1 : ∀ i < 57, s1.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
    fun i hi => o1 _ (Or.inr (by have := hfar i hi; simp only [KC]; omega))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadsS_ok s1 ((g1 _ (by decide)).trans hp) (fun i hi => by
    rw [rd1, wr1]; exact hr8 i hi)) fun s2 ⟨v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W s2 .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 128)) (kOffs.map fun d => .mem (sc d))
    (word s2.mem base 128) (kOffs.map fun d => word s2.mem base d)
    (fun _ h => h) W_nodup rfl
    (stable_sc hs2 (by decide) (by decide))
    (stable_scs hs2 (by decide) VG.Proof.Ed448.X86_64.kOffs (by decide))) fun s3 ⟨c, hc, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have p3 : s3.gpr .rsi = p := by rw [k3.1 _ (by decide), k2.1 _ (by decide), g1 _ (by decide), hp]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.sTail_ok s3 p3 hc (by rw [k3.2.2.1, k3.2.2.2, k2.2.2.1, k2.2.2.2, rd1, wr1]; exact hr56))
    fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide) (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.orBad_ok hs4) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  have m3 : s3.mem = s1.mem := k3.2.1.trans k2.2.1
  refine ⟨s4.gpr .rdx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d4]
    have hkv : wv (word s2.mem base 128 :: kOffs.map fun d => word s2.mem base d) =
        2 ^ 448 - Spec.Ed448.L := by
      rw [← VG.Proof.Ed448.X86_64.kWords_val, ← k1, k2.2.1]; rfl
    have hy : rv s2 W = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
      rw [v2, ← VG.Proof.X448.X86_64.leNum_bytesAt_mv, Proof.Ed448.decodeLE_eq]
      refine congrArg Proof.X25519.leNum ?_
      simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt, off, BitVec.add_zero]
      exact List.map_congr_left fun i hi => hb1 i (by simp at hi; omega)
    have hb : s3.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
      rw [m3]; exact hb1 56 (by decide)
    rw [hkv, VG.Proof.Ed448.X86_64.len7, show rv s2 (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = rv s2 W from rfl, hy,
      show rv s3 (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = rv s3 W from rfl] at e3
    rw [VG.Proof.Ed448.X86_64.bytesAt_57, Proof.Ed448.decodeLE_append, hb]
    have hlen : (Spec.Ed448.bytesAt s.mem p 56).length = 56 := by simp [Spec.Ed448.bytesAt]
    rw [hlen, show Spec.Ed448.decodeLE [s.mem (p + BitVec.ofNat 64 56)] = (s.mem (p + BitVec.ofNat 64 56)).toNat by
      simp [Spec.Ed448.decodeLE]]
    have hyl : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < 2 ^ 448 := by
      have := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt s.mem p 56)
      rw [hlen] at this
      exact Nat.lt_of_lt_of_le this (by decide +kernel)
    have hrl := VG.Proof.X448.X86_64.rv_lt s3 W
    rw [len_W] at hrl
    have hc1 : c.toNat ≤ 1 := by cases c <;> decide
    have key := Proof.Ed448.sCheck_nat (b := (s.mem (p + BitVec.ofNat 64 56)).toNat) hyl hrl hc1 e3
    rw [← key]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, by rw [h]; rfl⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, BitVec.eq_of_toNat_eq h2⟩
      cases c with
      | false => rfl
      | true => exact absurd h1 (by decide)
  · rw [mt, word_writeW_self, m4, m3, o1.word (Or.inr (by decide)) (by decide)]
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    rw [gt r h1, g4 r h1 h2, k3.1 r h3, k2.1 r h3, g1 r h3]
  · rw [rdt, rd4, k3.2.2.1, k2.2.2.1, rd1]
  · rw [wrt, wr4, k3.2.2.2, k2.2.2.2, wr1]
  · intro x hx hy
    rw [mt, (writeW_outside s4.mem base _ (by decide)) x hy, m4, m3]
    exact o1 x hx

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode`. -/
section

/-!
# Ed448 verification's equation on x86-64: decoding a point

`decode fld xo yo` on the 57 bytes at `rsi` (RFC 8032 §5.2.3): `y`'s words
and the sign bit (`decodeY_ok`), `u`, `v`, `u³v` and `u⁵v³` (`decodeUV`),
the power by `(p-3)/4` (`root_spec`), `x` and the check `v x² = u`
(`decodeX_ok`), and the sign (`decodeSign_ok`). `decode_ok`: `BAD` gains a
word that is 0 exactly when the bytes decode, and then slots `xo` and `yo`
hold the decoded point's coordinates (`Z = 1`).
-/

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside Outside2 ofs writeW_outside word_writeW_self contains_sc rv mv fe E
  Index Keeps freeze_ok stores_ok val7 mv7 rvW slot_lt W_len)
open VG.Impl.X448.X86_64 (W w sc at_ slot)

theorem byteBlock_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.movzx8 .rdx (at_ .rsi 56), .mov .rax (.reg .rdx), .shift .shr .rax 7,
      .store (sc SIGN) .rax, .alu .and .rdx (.imm 0x7f)] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base SIGN) (BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128)) ∧
      t.gpr .rdx = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wb : InRegions s.wr (base + BitVec.ofNat 64 SIGN) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [hp, hr, hs.rdi, wb]
  have hb := (s.mem (p + 56#64)).isLt
  refine ⟨?_, ?_, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (127 : BitVec 32)).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : BitVec.toNat (s.mem (p + 56#64)) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : BitVec.toNat (s.mem (p + 56#64)) % 128 < 2 ^ 64)]

theorem E_outside2 {base : Addr} {m m' : Mem} {o : Nat} (h : Outside2 base o 56 BAD 80 m m') (i : Index)
    (hi : slot i.val + 56 ≤ o ∨ o + 56 ≤ slot i.val) : VG.Proof.X448.X86_64.E m' base i = VG.Proof.X448.X86_64.E m base i := by
  have := slot_lt i
  simp only [VG.Impl.X448.X86_64.ACC] at this
  show VG.Proof.X448.toFe (mv m' base (slot i.val) 7) = VG.Proof.X448.toFe (mv m base (slot i.val) 7)
  rw [h.mv (by omega) (Or.inl (by simp only [BAD]; omega)) (by omega)]

theorem decodeY_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p) (yo : Index)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (.block (decodeY yo.val)) s fun t =>
      VG.Proof.X448.X86_64.E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      word t.mem base SIGN = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ yo → VG.Proof.X448.X86_64.E t.mem base i = VG.Proof.X448.X86_64.E s.mem base i) ∧
      (∀ r, r ∉ Reg.rax :: Reg.rdx :: Reg.r15 :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base (slot yo.val) 56 BAD 80 s.mem t.mem := by
  have hy := slot_lt yo
  simp only [VG.Impl.X448.X86_64.ACC] at hy
  rw [decodeY, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.loadsS_ok s hp hr8) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs1 (slot yo.val) W (by rw [W_len]; omega)) fun s2 ⟨v2, o2, g2, rd2, wr2⟩ => ?_
  rw [W_len] at v2 o2
  have hs2 : Scr s2 base := ⟨(g2 _).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have b2 : s2.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [o2 _ (Or.inr (by have := hfar 56 (by decide); omega)), k1.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.byteBlock_ok hs2 ((g2 _).trans ((k1.1 _ (by decide)).trans hp))
    (by rw [rd2, wr2, k1.2.2.1, k1.2.2.2]; exact hr56)) fun s3 ⟨m3, d3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide) (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.orBad_ok hs3) fun s4 ⟨m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 (a := slot yo.val) hy) fun s5 ⟨v5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.diffWords_ok hs5 (o := slot yo.val) (by omega)) fun s6 ⟨d6, m6, g6, rd6, wr6⟩ => ?_
  have hs6 : Scr s6 base := ⟨(g6 _ (by decide) (by decide)).trans hs5.rdi, wr6 ▸ hs5.wr, hs5.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.orBad_ok hs6) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  have hy0 : mv s.mem p 0 7 = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [← VG.Proof.X448.X86_64.leNum_bytesAt_mv, Proof.Ed448.decodeLE_eq]
    refine congrArg Proof.X25519.leNum ?_
    simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt, off, BitVec.add_zero]
  have O23 : Outside base SIGN 8 s2.mem s3.mem := by rw [m3]; exact writeW_outside _ _ _ (by decide)
  have O34 : Outside base BAD 8 s3.mem s4.mem := by rw [m4]; exact writeW_outside _ _ _ (by decide)
  have O6t : Outside base BAD 8 s6.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have hY5 : mv s5.mem base (slot yo.val) 7 = mv s2.mem base (slot yo.val) 7 := by
    rw [k5.2.1, O34.mv (Or.inl (by simp only [BAD]; omega)) (by omega),
      O23.mv (Or.inl (by simp only [SIGN]; omega)) (by omega)]
  have hYt : mv t.mem base (slot yo.val) 7 = mv s5.mem base (slot yo.val) 7 := by
    rw [O6t.mv (Or.inl (by simp only [BAD]; omega)) (by omega), m6]
  have hYv : mv s5.mem base (slot yo.val) 7 = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [hY5, v2, v1, hy0]
  have F : Outside2 base (slot yo.val) 56 BAD 80 s.mem t.mem := by
    intro x h1 h2
    simp only [BAD] at h2 O6t O34
    simp only [SIGN] at O23
    rw [O6t x (by omega), m6, k5.2.1, O34 x (by omega), O23 x (by omega), o2 x h1, k1.2.1]
  refine ⟨?_, ?_, ⟨BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ||| s6.gpr .rdx, ?_, ?_⟩,
    fun i hi => VG.Proof.Ed448.X86_64.E_outside2 F i (by
      have := Fin.val_ne_of_ne hi
      simp only [slot]; omega), ?_, ?_, ?_, F⟩
  · show VG.Proof.X448.toFe (mv t.mem base (slot yo.val) 7) = _
    rw [hYt, hYv]
  · rw [O6t.word (Or.inr (by decide)) (by decide), m6, k5.2.1, O34.word (Or.inr (by decide)) (by decide), m3,
      word_writeW_self, b2]
  · rw [VG.Proof.Ed448.X86_64.or_eq_zero64, d6, ← hYv]
    have e1 : BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) = 0 ↔
        (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · intro h; rw [h]; rfl
    have e2 : (∀ i < 7, word s5.mem base (slot yo.val + 8 * i) = s5.gpr (w i)) ↔
        mv s5.mem base (slot yo.val) 7 < Spec.X448.P := by
      have hP0 : Spec.X448.P ≠ 0 := by decide +kernel
      have hv : rv s5 W = mv s5.mem base (slot yo.val) 7 % Spec.X448.P := by
        rw [v5, ← k5.2.1]
      have key : (∀ i < 7, word s5.mem base (slot yo.val + 8 * i) = s5.gpr (w i)) ↔
          mv s5.mem base (slot yo.val) 7 = rv s5 W := by
        rw [mv7, rvW, VG.Proof.Ed448.X86_64.val7_inj (fun i _ => BitVec.isLt _) (fun i _ => BitVec.isLt _)]
        constructor
        · intro h i hi; exact congrArg BitVec.toNat (h i hi)
        · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)
      rw [key, hv, eq_comm, Nat.mod_eq_iff_lt hP0]
    rw [e1, e2]
  · rw [mt, word_writeW_self, m6, k5.2.1, m4, word_writeW_self, d3, b2, BitVec.or_assoc,
      O23.word (Or.inl (by decide)) (by decide), o2.word (Or.inr (by simp only [BAD]; omega)) (by decide),
      k1.2.1]
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [gt r h1, g6 r h1 h2, k5.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩), g4 r h1,
      g3 r h1 h2, g2, k1.1 r h4]
  · rw [rdt, rd6, k5.2.2.1, rd4, rd3, rd2, k1.2.2.1]
  · rw [wrt, wr6, k5.2.2.2, wr4, wr3, wr2, k1.2.2.2]

theorem or7 (f : Nat → BitVec 64) :
    (f 0 ||| f 1 ||| f 2 ||| f 3 ||| f 4 ||| f 5 ||| f 6 = 0) ↔ ∀ i < 7, f i = 0 := by
  simp only [VG.Proof.Ed448.X86_64.or_eq_zero64]
  constructor
  · intro h i hi
    match i, hi with
    | 0, _ => exact h.1.1.1.1.1.1
    | 1, _ => exact h.1.1.1.1.1.2
    | 2, _ => exact h.1.1.1.1.2
    | 3, _ => exact h.1.1.1.2
    | 4, _ => exact h.1.1.2
    | 5, _ => exact h.1.2
    | 6, _ => exact h.2
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h 0 (by decide), h 1 (by decide)⟩, h 2 (by decide)⟩, h 3 (by decide)⟩, h 4 (by decide)⟩,
      h 5 (by decide)⟩, h 6 (by decide)⟩

theorem negMask (x : BitVec 64) {sb : Nat} (hsb : sb < 2) :
    BitVec.setWidth 64 (0 : BitVec 32) - (x &&& BitVec.signExtend 64 (1 : BitVec 32) ^^^ BitVec.ofNat 64 sb) =
      VG.Proof.X448.X86_64.mask (decide (x.toNat % 2 ≠ sb)) := by
  have ha : x &&& BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.toNat % 2 < 2 ^ 64)]
  rw [ha]
  have h2 : x.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 2 = a at *
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    decide

/-- The mask of `x`'s low bit differing from the sign bit, and the OR of `x`'s words. -/
theorem signA_ok {s : State} {base : Addr} (hs : Scr s base) {sb : Nat} (hsb : word s.mem base SIGN = BitVec.ofNat 64 sb)
    (hsb2 : sb < 2) :
    WP isa (.block (([.mov .rcx (.reg .r8), .alu .and .rcx (.imm 1), .mov .rax (.mem (sc SIGN)),
      .alu .xor .rcx (.reg .rax), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx), .store (sc NEG) .rdx,
      .mov .rdx (.reg .r8)] : List Instr) ++ (List.range 6).map (fun i => Instr.alu .or .rdx (.reg (w (i + 1)))))) s fun t =>
      t.mem = s.mem.writeW (off base NEG)
        (VG.Proof.X448.X86_64.mask (decide ((s.gpr .r8).toNat % 2 ≠ sb))) ∧
      t.gpr .rax = BitVec.ofNat 64 sb ∧
      (t.gpr .rdx = 0 ↔ ∀ i < 7, s.gpr (w i) = 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 SIGN) 8 := hs.read (by decide)
  have wb : InRegions s.wr (base + BitVec.ofNat 64 NEG) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [hs.rdi, rb, wb, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, w, W, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd, List.cons_append,
    List.append_assoc, List.singleton_append]
  rw [show s.mem.readW (base + BitVec.ofNat 64 SIGN) 64 = BitVec.ofNat 64 sb from hsb]
  refine ⟨by rw [VG.Proof.Ed448.X86_64.negMask _ hsb2], rfl,
    VG.Proof.Ed448.X86_64.or7 (fun i => s.gpr ([Reg.r8, Reg.r9, Reg.r10, Reg.r11, Reg.r12, Reg.r13, Reg.r14].getD i Reg.r8)),
    fun r h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

open VG.Proof.X448.X86_64 (FieldOk Keep cswapE opSwap mask)

theorem rvW_mod2 (s : State) : rv s W % 2 = (s.gpr .r8).toNat % 2 := by
  simp only [rv, W]; omega

theorem rvW_zero (s : State) : (∀ i < 7, s.gpr (w i) = 0) ↔ rv s W = 0 := by
  rw [rvW, show (0 : Nat) = val7 (fun _ => 0) from rfl,
    VG.Proof.Ed448.X86_64.val7_inj (fun i _ => BitVec.isLt _) (fun _ _ => by decide)]
  constructor
  · intro h i hi; rw [h i hi]; rfl
  · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)

theorem andRax_ok (s : State) :
    WP isa (.block ([.alu .and .rdx (.reg .rax)] : List Instr)) s fun t =>
      t.gpr .rdx = s.gpr .rdx &&& s.gpr .rax ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r hr => by simp only [hr, ite_false]

theorem movNeg_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov .rcx (.mem (sc NEG))] : List Instr)) s fun t =>
      t.gpr .rcx = word s.mem base NEG ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 NEG) 8 := hs.read (by decide)
  erun [hs.rdi, rb]
  exact fun r hr => by simp only [hr, ite_false]

theorem sign_bit (a sb : Nat) (ha : a < 2) (hsb : sb < 2) :
    ((a == 1) == (sb == 1)) = !(decide (a ≠ sb)) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    decide

theorem zeroSign (z : Bool) (sb : Nat) (hsb : sb < 2) :
    ((if z then (1 : BitVec 64) else 0) &&& BitVec.ofNat 64 sb = 0 ↔ ¬ (z = true ∧ sb = 1)) := by
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> cases z <;> decide

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem decodeSign_ok {s : State} {base : Addr} (hs : Scr s base) (xo : Index) (hxo : xo = 6 ∨ xo = 8)
    {sb : Nat} (hsb : word s.mem base SIGN = BitVec.ofNat 64 sb) (hsb2 : sb < 2) :
    WP isa (.block (decodeSign fld xo.val)) s fun t =>
      VG.Proof.X448.X86_64.E t.mem base xo = (if ((VG.Proof.X448.X86_64.E s.mem base xo).val % 2 == 1) == (sb == 1) then VG.Proof.X448.X86_64.E s.mem base xo
        else (VG.Proof.X448.X86_64.E s.mem base xo - VG.Proof.X448.X86_64.E s.mem base xo) - VG.Proof.X448.X86_64.E s.mem base xo) ∧
      (∃ c : BitVec 64, (c = 0 ↔ ¬ (VG.Proof.X448.X86_64.E s.mem base xo = 0 ∧ sb = 1)) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ xo → i ≠ 12 → VG.Proof.X448.X86_64.E t.mem base i = VG.Proof.X448.X86_64.E s.mem base i) ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  have hx := slot_lt xo
  simp only [VG.Impl.X448.X86_64.ACC] at hx
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  rw [show decodeSign fld xo.val = VG.Impl.X448.X86_64.freeze (slot xo.val) ++ (([.mov .rcx (.reg .r8), .alu .and .rcx (.imm 1),
      .mov .rax (.mem (sc SIGN)), .alu .xor .rcx (.reg .rax), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx),
      .store (sc NEG) .rdx, .mov .rdx (.reg .r8)] ++
      (List.range 6).map (fun i => Instr.alu .or .rdx (.reg (w (i + 1))))) ++ (isZero ++
      (([.alu .and .rdx (.reg .rax)] : List Instr) ++ (orBad ++ (fieldCode fld [.sub 12 xo.val xo.val, .sub 12 12 xo.val] ++
      (([.mov .rcx (.mem (sc NEG))] : List Instr) ++ VG.Impl.X448.X86_64.cswap (slot xo.val) (slot 12))))))) by
    simp only [decodeSign, List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs (a := slot xo.val) hx) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.signA_ok hs1 (by rw [k1.2.1]; exact hsb) hsb2) fun s2 ⟨m2, a2, d2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide) (by decide) (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.isZero_ok s2) fun s3 ⟨d3, m3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.andRax_ok s3) fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.orBad_ok hs4) fun s5 ⟨m5, g5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs4.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.fieldCode_ok hf [.sub 12 xo.val xo.val, .sub 12 12 xo.val]
    (by rcases hxo with rfl | rfl <;> decide) hs5) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.movNeg_ok hs6) fun s7 ⟨c7, m7, g7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs6.nowrap⟩
  have hxv : rv s1 W = (VG.Proof.X448.X86_64.E s.mem base xo).val := by rw [v1]; rfl
  have hsw : decide ((s1.gpr .r8).toNat % 2 ≠ sb) = decide ((VG.Proof.X448.X86_64.E s.mem base xo).val % 2 ≠ sb) := by
    rw [← VG.Proof.Ed448.X86_64.rvW_mod2, hxv]
  have O5 : Outside base BAD 80 s.mem s5.mem := by
    intro x hx
    rw [m5, writeW_outside s4.mem base _ (by decide) x (by simp only [BAD] at hx ⊢; omega), m4, m3, m2,
      writeW_outside s1.mem base _ (by decide) x (by simp only [BAD, NEG] at hx ⊢; omega), k1.2.1]
  have e5 : VG.Proof.X448.X86_64.E s5.mem base = VG.Proof.X448.X86_64.E s.mem base := VG.Proof.Ed448.X86_64.E_bad O5
  obtain ⟨n12, nk⟩ := subNeg_eval xo hx12 (VG.Proof.X448.X86_64.E s5.mem base)
  have hneg : word s6.mem base NEG = mask (decide ((VG.Proof.X448.X86_64.E s.mem base xo).val % 2 ≠ sb)) := by
    rw [k6.mem.word (Or.inr (by decide)) (by decide), m5, (writeW_outside s4.mem base _ (by decide)).word
      (Or.inr (by decide)) (by decide), m4, m3, m2, word_writeW_self, hsw]
  refine WP.mono (cswapE hs7 xo 12 hx12 (sw := decide ((VG.Proof.X448.X86_64.E s.mem base xo).val % 2 ≠ sb))
    (by rw [c7, hneg])) fun t ⟨kt, _, et⟩ => ?_
  have e6 : VG.Proof.X448.X86_64.E s7.mem base = evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] (VG.Proof.X448.X86_64.E s5.mem base) := by
    rw [m7, e6]
  have hx2 : (VG.Proof.X448.X86_64.E s.mem base xo).val % 2 < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ⟨s4.gpr .rdx, ?_, ?_⟩, fun i h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [et, VG.Proof.Ed448.X86_64.sign_bit _ _ hx2 hsb2]
    cases hd : decide ((VG.Proof.X448.X86_64.E s.mem base xo).val % 2 ≠ sb) with
    | false =>
      simp only [opSwap, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne hx12, Function.update_self, e6, nk xo hx12, e5]
    | true =>
      simp only [opSwap, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne hx12, Function.update_self, e6, n12, e5]
  · rw [d4, d3, g3 _ (by decide), a2]
    have hz : (s2.gpr .rdx = 0) ↔ VG.Proof.X448.X86_64.E s.mem base xo = 0 := by
      rw [d2, VG.Proof.Ed448.X86_64.rvW_zero, hxv]
      have z0 : (0 : Spec.X448.Fe).val = 0 := by decide +kernel
      constructor
      · intro h; exact Fin.ext (h.trans z0.symm)
      · intro h; rw [h]; exact z0
    by_cases h0 : s2.gpr .rdx = 0
    · rw [ite_eq_left h0]
      have := VG.Proof.Ed448.X86_64.zeroSign true sb hsb2
      simp only [ite_true] at this
      rw [this, hz.mp h0]
      exact ⟨fun h1 h2 => h1 ⟨trivial, h2.2⟩, fun h1 h2 => h1 ⟨rfl, h2.2⟩⟩
    · rw [ite_eq_right h0]
      have := VG.Proof.Ed448.X86_64.zeroSign false sb hsb2
      simp only [Bool.false_eq_true, ite_false] at this
      rw [this]
      constructor
      · intro _ h; exact h0 (hz.mpr h.1)
      · intro _ h; exact h.1.elim
  · rw [kt.mem.word (Or.inr (by decide)) (by decide), m7, k6.mem.word (Or.inr (by decide)) (by decide), m5,
      word_writeW_self, m4, m3, m2, (writeW_outside s1.mem base _ (by decide)).word (Or.inl (by decide))
      (by decide), k1.2.1]
  · rw [et]
    simp only [opSwap]
    rw [Function.update_of_ne h2, Function.update_of_ne h1, e6, nk i h2, e5]
  · have hr' : ∀ x ∈ Reg.rax :: Reg.r15 :: W, x ∈ VG.Proof.X448.X86_64.clob := by decide
    rw [kt.gpr r hr, g7 r (fun h => hr (h ▸ by decide)), k6.gpr r hr, g5 r (fun h => hr (h ▸ by decide)),
      g4 r (fun h => hr (h ▸ by decide)), g3 r (fun h => hr (h ▸ by decide)),
      g2 r (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)),
      k1.1 r (fun h => hr (hr' r h))]
  · rw [kt.rd, rd7, k6.rd, rd5, rd4, rd3, rd2, k1.2.2.1]
  · rw [kt.wr, wr7, k6.wr, wr5, wr4, wr3, wr2, k1.2.2.2]
  · intro x h1 h2
    rw [kt.mem x h1, m7, k6.mem x h1, O5 x h2]

include hf in
theorem decodeX_ok {s : State} {base : Addr} (hs : Scr s base) (xo : Index) (hxo : xo = 6 ∨ xo = 8) :
    WP isa (.block (decodeX fld xo.val)) s fun t =>
      VG.Proof.X448.X86_64.E t.mem base xo = VG.Proof.X448.X86_64.E s.mem base xo * VG.Proof.X448.X86_64.E s.mem base 21 ∧
      (∃ c : BitVec 64, (c = 0 ↔ VG.Proof.X448.X86_64.E s.mem base 3 * ((VG.Proof.X448.X86_64.E s.mem base xo * VG.Proof.X448.X86_64.E s.mem base 21) *
          (VG.Proof.X448.X86_64.E s.mem base xo * VG.Proof.X448.X86_64.E s.mem base 21)) = VG.Proof.X448.X86_64.E s.mem base 13) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ xo → i ≠ 12 → VG.Proof.X448.X86_64.E t.mem base i = VG.Proof.X448.X86_64.E s.mem base i) ∧
      word t.mem base SIGN = word s.mem base SIGN ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [decodeX, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.fieldCode_ok hf [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12]
    (by rcases hxo with rfl | rfl <;> decide) hs) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
  obtain ⟨x1, x12, x13, xk⟩ := decodeXOps_eval xo hxo (VG.Proof.X448.X86_64.E s.mem base)
  refine WP.mono (VG.Proof.Ed448.X86_64.eqSlots_ok hs1 12 13) fun t ⟨c, hc, ht, kt, st⟩ => ?_
  rw [kt.E, e1]
  refine ⟨x1, ⟨c, by rw [hc, e1, x12, x13], by rw [ht, k1.mem.word (Or.inr (by decide)) (by decide)]⟩,
    fun i h1 h2 => xk i h1 h2, by rw [st, k1.mem.word (Or.inr (by decide)) (by decide)],
    fun r hr => ?_, by rw [kt.rd, k1.rd], by rw [kt.wr, k1.wr], fun x h1 h2 => by
      rw [kt.mem x h2, k1.mem x h1]⟩
  have : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ VG.Proof.X448.X86_64.clob := by decide
  rw [kt.gpr r (fun h => hr (this r h)), k1.gpr r hr]

open VG.Proof.X448.X86_64 (IKeep)

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

include hf in
theorem decode_ok (hR : RecoverOk) {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p)
    (xo yo : Index)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (h10 : VG.Proof.X448.X86_64.E s.mem base 10 = 1) (h11 : VG.Proof.X448.X86_64.E s.mem base 11 = Spec.Ed448.d)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (decode fld xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        VG.Proof.X448.X86_64.E t.mem base xo = pt.X ∧ VG.Proof.X448.X86_64.E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Index, i.val < 12 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → i ≠ yo →
        VG.Proof.X448.X86_64.E t.mem base i = VG.Proof.X448.X86_64.E s.mem base i) ∧
      (∀ r, r ∉ .rbx :: VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy := slot_lt yo
  simp only [VG.Impl.X448.X86_64.ACC] at hy
  rw [decode]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.decodeY_ok hs hp yo hr8 hr56 hfar) fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, g1, rd1, wr1, o1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.Ed448.X86_64.fieldCode_ok hf (decodeUV yo.val xo.val)
    (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  apply WP.seq
  refine WP.mono (VG.Proof.Ed448.X86_64.root_spec hf base s2 hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86_64.decodeX_ok hf hs3 xo hxo) fun s4 ⟨x4, ⟨c2, hc2, b4⟩, e4, sg4, g4, rd4, wr4, o4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  have hb128 : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega
  have sg : word s4.mem base SIGN = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [sg4, k3.mem.word (Or.inr (by decide)) (by decide), k2.mem.word (Or.inr (by decide)) (by decide), sg1]
  refine WP.mono (VG.Proof.Ed448.X86_64.decodeSign_ok hf hs4 xo hxo sg hb128)
    fun t ⟨xt, ⟨c3, hc3, bt⟩, et, gt, rdt, wrt, ot⟩ => ?_
  -- The values.
  have h10' : VG.Proof.X448.X86_64.E s1.mem base 10 = 1 := by
    rw [e1 10 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : VG.Proof.X448.X86_64.E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2, k2'⟩ := decodeUV_eval xo yo hxy (VG.Proof.X448.X86_64.E s1.mem base)
  simp only [h10', h11', y1] at u2 v2 t2 w2
  simp only [← e2] at u2 v2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  have r21 : VG.Proof.X448.X86_64.E s3.mem base 21 = rootPow (VG.Proof.X448.X86_64.E s2.mem base 12) := by rw [e3, VG.Proof.Ed448.X86_64.rootEnv_eval]
  have r3k : ∀ i : Index, i.val < 14 → VG.Proof.X448.X86_64.E s3.mem base i = VG.Proof.X448.X86_64.E s2.mem base i := fun i hi => by
    rw [e3, VG.Proof.Ed448.X86_64.rootEnv_keep _ _ hi]
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  rw [r3k xo hxlt, t2, r21, w2, r3k 3 (by decide), v2, r3k 13 (by decide), u2] at hc2
  rw [r3k xo hxlt, t2, r21, w2] at x4
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  rw [x4] at xt hc3
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem p 57) (VG.Proof.Ed448.X86_64.bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [VG.Proof.Ed448.X86_64.bytesAt57_take]) (by rw [VG.Proof.Ed448.X86_64.bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  -- what is kept
  have kY : VG.Proof.X448.X86_64.E t.mem base yo = Y := by
    rw [et yo hyx (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide),
      e4 yo hyx (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h3 h4 h5 hix hiy => ?_, fun r hr => ?_,
    ?_, ?_, ?_⟩
  · rw [VG.Proof.Ed448.X86_64.or_eq_zero64, VG.Proof.Ed448.X86_64.or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [bt, b4, k3.mem.word (Or.inr (by decide)) (by decide), k2.mem.word (Or.inr (by decide)) (by decide),
      b1]
    simp only [BitVec.or_assoc]
  · rw [hD] at hpt
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at hpt
      cases hpt
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at hpt
      cases hpt
  · have hi14 : i.val < 14 := by omega
    have h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    have h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [et i hix h12, e4 i hix h12, r3k i hi14, k2' i h3 h4 h5 h12 h13 hix, e1 i hiy]
  · have s1 : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ Reg.rbx :: VG.Proof.X448.X86_64.clob := by decide
    have hr' : r ∉ VG.Proof.X448.X86_64.clob := fun h => hr (List.mem_cons_of_mem _ h)
    have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self)
    rw [gt r hr', g4 r hr', k3.gpr r hr' hrb, k2.gpr r hr', g1 r (fun h => hr (s1 r h))]
  · rw [rdt, rd4, k3.rd, k2.rd, rd1]
  · rw [wrt, wr4, k3.wr, k2.wr, wr1]
  · intro z h1 h2
    have hy2 := o1 z (by
      rcases h1 with h | h
      · left; have := slot_lt yo; simp only [slot] at *; omega
      · right; simp only [slot] at *; omega) h2
    rw [ot z h1 h2, o4 z h1 h2, k3.mem z (by omega), k2.mem z h1, hy2]

end VG.Proof.Ed448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86_64.Words57`. -/
section

/-!
# Ed448 on x86-64: 57-byte strings as words

The number of 57 bytes in memory as seven words and a byte (`decode57`), as
the code that prunes a hash into a scalar reads it.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- The 57 bytes at `p`: seven words and a byte. -/
theorem decode57 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 57) =
      (m.readW p 64).toNat + 2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 8) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 16) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 24) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 32) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 40) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 48) 64).toNat + 2 ^ 64 *
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 56) 1))))))) := by
  have e0 := VG.Proof.Ed448.X86_64.words_step m p 57 0 (by omega)
  have e1 := VG.Proof.Ed448.X86_64.words_step m p 57 1 (by omega)
  have e2 := VG.Proof.Ed448.X86_64.words_step m p 57 2 (by omega)
  have e3 := VG.Proof.Ed448.X86_64.words_step m p 57 3 (by omega)
  have e4 := VG.Proof.Ed448.X86_64.words_step m p 57 4 (by omega)
  have e5 := VG.Proof.Ed448.X86_64.words_step m p 57 5 (by omega)
  have e6 := VG.Proof.Ed448.X86_64.words_step m p 57 6 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.sub_zero] at e0 e1 e2 e3 e4 e5 e6
  rw [BitVec.add_zero] at e0
  rw [e0, e1, e2, e3, e4, e5, e6]

/-- The byte below a word that is zero. -/
theorem byte_of_zero (m : Mem) (p : Addr) (h : m.readW p 64 = 0) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) = 0 := by
  have hs : Spec.Ed448.bytesAt m p (1 + 7) =
      Spec.Ed448.bytesAt m p 1 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 1) 7 :=
    Proof.X25519.bytesAt_add m p 1 7
  have hw : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 8) = 0 := by
    rw [Proof.Ed448.decodeLE_eq, Proof.Ed448.bytesAt_eq, Proof.X25519.leNum_bytesAt_64, h]; rfl
  rw [show (8 : Nat) = 1 + 7 from rfl, hs, Proof.Ed448.decodeLE_append] at hw
  omega

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem decodeLE_byte_lt (m : Mem) (p : Addr) : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) < 256 := by
  simp only [Spec.Ed448.bytesAt, List.range_one, List.map_cons, List.map_nil, Spec.Ed448.decodeLE]
  have := (m (p + BitVec.ofNat 64 0)).isLt
  omega

end VG.Proof.Ed448.X86_64

end
