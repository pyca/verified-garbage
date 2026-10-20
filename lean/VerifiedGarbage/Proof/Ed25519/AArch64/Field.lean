module

public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mul
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.Sub
public import VerifiedGarbage.Spec.Ed25519
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Merged from `Proof.Ed25519.AArch64.Sqr`. -/

@[expose] public section

section
/-! Four-word field squaring. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem sq_expand_radix (R A0 A1 A2 A3 : Nat) :
    (A0 + R * A1 + R * R * A2 + R * R * R * A3) * (A0 + R * A1 + R * R * A2 + R * R * R * A3) =
      R * (2 * (A0 * A1 + R * (A0 * A2) + R * R * (A0 * A3 + A1 * A2) + R * R * R * (A1 * A3) +
        R * R * R * R * (A2 * A3))) +
        (A0 * A0 + R * R * (A1 * A1) + R * R * R * R * (A2 * A2 + R * R * (A3 * A3))) := by
  grind

/-- The square of four words: twice the products of distinct words, and the squares. -/
theorem sq_expand (A0 A1 A2 A3 : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) *
        (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) =
      2 ^ 64 * (2 * cross A0 A1 A2 A3) + diag A0 A1 A2 A3 := by
  have h := sq_expand_radix (2 ^ 64) A0 A1 A2 A3
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from rfl,
    show (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 from rfl,
    show (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 from rfl] at h
  exact h

theorem sqrWide_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat}
    (ha : FieldRange a large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (sqrWide a)) s fun t =>
      wide t = fe s.mem base a * fe s.mem base a ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x21, .x22, .x23, .x24] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [sqrWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ha (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sqrCross_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrDouble_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (sqrDiag_ok s₃) fun s₄ ⟨c, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have A : ∀ (r : Reg), r ∈ [.x12, .x13, .x14, .x15] → s₃.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  rw [A .x12 (by decide), A .x13 (by decide), A .x14 (by decide), A .x15 (by decide),
    e3, e2, a0, a1, a2, a3] at e4
  have hlt : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  have hx := sq_expand (word s.mem base a).toNat (word s.mem base (a + 8)).toNat
    (word s.mem base (a + 16)).toNat (word s.mem base (a + 24)).toNat
  dsimp only [wide]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx] at hlt
  omega_using [e4, hlt]

/-- Squaring modulo p, allowing the output to alias the input. -/
theorem sqr_okB {s : State} {base : Addr} (hs : Scr s base large) {o a : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) :
    WP isa (.block (fieldSqr o a)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a ∧
        fe t.mem base o < 2 ^ 255 + 2 ^ 135 := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldSqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrWide_ok hs₀ ha hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht, hb⟩ => ⟨hop, ?_, hb⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base large) {o a : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) :
    WP isa (.block (fieldSqr o a)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a :=
  WP.mono (sqr_okB hs ho ha) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

theorem movReg_ok (s : State) (d n : Reg) :
    WP isa (.block [mov d n]) s fun t => t.gpr d = s.gpr n ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 0) (by decide), WP.block_nil_iff.mpr
    ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

/-- `movB`: x4–x7 into x12–x15. -/
theorem movB_ok (s : State) :
    WP isa (.block movB) s fun t =>
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ∧
      Keeps [.x12, .x13, .x14, .x15] s t := by
  rw [show movB = ([mov .x12 .x4] : List Instr) ++ (([mov .x13 .x5] : List Instr) ++
    (([mov .x14 .x6] : List Instr) ++ ([mov .x15 .x7] : List Instr))) from rfl,
    WP.block_append_iff]
  refine WP.mono (movReg_ok s .x12 .x4) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₁ .x13 .x5) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₂ .x14 .x6) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (movReg_ok s₃ .x15 .x7) fun t ⟨e4, k4⟩ => ⟨?_, ?_⟩
  · rw [e4, k4.gpr .x12 (by decide), k4.gpr .x13 (by decide), k4.gpr .x14 (by decide),
      k3.gpr .x12 (by decide), k3.gpr .x13 (by decide), e3, k2.gpr .x12 (by decide), e2, e1,
      k3.gpr .x7 (by decide), k2.gpr .x7 (by decide), k1.gpr .x7 (by decide),
      k2.gpr .x6 (by decide), k1.gpr .x6 (by decide), k1.gpr .x5 (by decide)]
  · exact ((k1.mono (by decide)).trans (k2.mono (by decide))).trans
      ((k3.mono (by decide)).trans (k4.mono (by decide)))

/-- `[o] := [a] · [b]²`, allowing the output to alias either input; the result is
stored below `2²⁵⁵ + 2¹³⁵`. -/
theorem sqrMul_okB {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldSqrMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * (F s.mem base b * F s.mem base b) ∧
        fe t.mem base o < 2 ^ 255 + 2 ^ 135 := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [fieldSqrMul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrWide_ok hs₀ hb hz) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceWide_ok s₁ ((k1.gpr _ (by decide)).trans hz)) fun s₂ ⟨e2, z2, k2, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movB_ok s₂) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  have z3 : s₃.gpr .x10 = 0 := (k3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (mulRows_ok hs₃ ha z3 e3) fun s₄ ⟨e4, k4⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₃.of_keeps k4 (by decide)) ho
    ((k4.gpr _ (by decide)).trans z3)
    ((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      ((k3.mono (by decide)).trans (k4.mono (by decide)))))
    fun t ⟨hop, ht, hb⟩ => ⟨hop, ?_, hb⟩
  have m3 : s₃.mem = s.mem := by rw [k3.mem, k2.mem, k1.mem, k0.mem]
  rw [ht, e4, m3]
  rw [toFe_mul rfl, e2, e1, k0.mem]
  exact congrArg _ (toFe_mul rfl)

/-- `[o] := [a] · [b]²`, allowing the output to alias either input. -/
theorem sqrMul_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldSqrMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * (F s.mem base b * F s.mem base b) :=
  WP.mono (sqrMul_okB hs ho ha hb) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.Add`. -/
section
/-! Four-word field addition. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldAddWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * c.toNat =
          fe s.mem base a + fe s.mem base b ∧
        (t.gpr .x8).toNat = 38 * c.toNat ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ workSize large → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) hd⟩
  have enc : ∀ d, d + 8 ≤ workSize large → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldAddWords, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, ld, exec, addr, State.load, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.mem_addWithCarry,
    BitVec.setWidth_eq, hs.x0, hz, h38, Size.bytes,
    Nat.add_mod, ha, hb, Nat.reduceMod, Nat.zero_add,
    enc a (by omega), enc b (by omega), enc (a + 8) (by omega), enc (b + 8) (by omega),
    enc (a + 16) (by omega), enc (b + 16) (by omega), enc (a + 24) (by omega), enc (b + 24) (by omega),
    w a (by omega), w b (by omega), w (a + 8) (by omega), w (b + 8) (by omega),
    w (a + 16) (by omega), w (b + 16) (by omega), w (a + 24) (by omega), w (b + 24) (by omega),
    and_self, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (word s.mem base (a + 24)) (word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (word s.mem base (b + 8))
        (carryOut (word s.mem base a) (word s.mem base b) false))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := add4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact carry38_sel _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- Addition modulo p, with memory and ABI frames. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldAdd o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldAdd, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by
    rw [x1]
    have := Bool.toNat_le c
    omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ heq => ?_
  subst s₃
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans k2')) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega), e2, x1]
  rw [k0.mem] at e1
  have hm : toFe (val4 (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7) + 38 * c.toNat) =
      toFe (fe s.mem base a + fe s.mem base b) := by
    apply toFe_congr
    rw [← e1]
    exact (fold256 _ _).symm
  exact hm.trans (toFe_add rfl)


theorem carry38Once_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block carry38Once) s fun t =>
      ∃ c : Bool, val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * c.toNat =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + (s.gpr .x8).toNat ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  rw [carry38Once]
  reg_exec hz
  refine ⟨carryOut (s.gpr .x7) 0 (carryOut (s.gpr .x6) 0
      (carryOut (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x8) false))), ?_,
    ⟨?_, by simp only [RegUpd.mem_addWithCarry], by simp only [RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_addWithCarry], by simp only [RegUpd.sp_addWithCarry]⟩⟩
  · have e0 := addCarry_value (s.gpr .x4) (s.gpr .x8) false
    have e1 := addCarry_value (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x8) false)
    have e2 := addCarry_value (s.gpr .x6) 0 (carryOut (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x8) false))
    have e3 := addCarry_value (s.gpr .x7) 0 (carryOut (s.gpr .x6) 0
      (carryOut (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x8) false)))
    dsimp only [addCarry, carryOut, Size.bits] at e0 e1 e2 e3 ⊢
    have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [val4, Bool.toNat_false, Nat.add_zero, z] at e0 e1 e2 e3 ⊢
    omega
  · reg_keeps

/-- Addition modulo p with one fold of the carry, for operands that sum below
`2²⁵⁷ − 38`. -/
theorem add1_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large)
    (hab : fe s.mem base a + fe s.mem base b < 2 ^ 257 - 38) :
    WP isa (.block (fieldAdd1 o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldAdd1, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  refine WP.mono (carry38Once_ok s₁ hz1) fun s₂ ⟨c', e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ heq => ?_
  subst s₃
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans k2')) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  rw [k0.mem] at e1
  have hl := val4_lt (s₂.gpr .x4) (s₂.gpr .x5) (s₂.gpr .x6) (s₂.gpr .x7)
  have hl1 := val4_lt (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7)
  have hc := Bool.toNat_le c
  have hc' := Bool.toNat_le c'
  have hsum : fe s.mem base a + fe s.mem base b =
      val4 (s₂.gpr .x4) (s₂.gpr .x5) (s₂.gpr .x6) (s₂.gpr .x7) + VG.Spec.X25519.P * (2 * c.toNat) := by
    simp only [VG.Spec.X25519.P]
    rw [x1] at e2
    omega
  apply toFe_add
  rw [hsum, Nat.add_mul_mod_self_left]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.FieldMemory`. -/
section
/-! Constants and copies in the field workspace. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem slot_rangeWith (o : Slot) : FieldRange (offset o) large := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  constructor <;> simp only [offset] <;> omega

theorem slot_range (o : Slot) : FieldRange (offset o) := slot_rangeWith (large := true) o

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = v.val ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  rw [constWords, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps [.x4, .x5, .x6, .x7] s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [k4.gpr .x4 (by decide), k3.gpr .x4 (by decide), k2.gpr .x4 (by decide), e1,
    k4.gpr .x5 (by decide), k3.gpr .x5 (by decide), e2, k4.gpr .x6 (by decide), e3, e4]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem constField_opB {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v ∧ fe t.mem base (offset o) = v.val := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [constField, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  have hf := fe_st4 t.mem base (o := offset o) (by have := (slot_rangeWith (large := large) o).2; omega)
    (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)
  refine ⟨Op.of_store (slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_, hf.trans hv⟩
  rw [F, hf, hv, toFe_self]

theorem constField_op {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v :=
  WP.mono (constField_opB hs o v) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base large) (a : Slot) :
    WP isa (.block (loads (offset a) .x4 .x5 .x6 .x7)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (offset a) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (loads_ok hs (slot_rangeWith (large := large) a) (by decide)) fun t ⟨e1, e2, e3, e4, k⟩ => ?_
  exact ⟨by rw [e1, e2, e3, e4], k⟩

theorem copyField_opB {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ fe t.mem base (offset o) = fe s.mem base (offset a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [copyField, WP.block_append_iff]
  refine WP.mono (loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [fe_st4 _ _ (by have := (slot_rangeWith (large := large) o).2; omega), hv]

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) :=
  WP.mono (copyField_opB hs o a) fun _ ⟨h, e⟩ => ⟨h, congrArg toFe e⟩

theorem Outside_F {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 32 < 2 ^ 64)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : F m' base d = F m base d :=
  congrArg toFe (h.fe hsep hd)

end VG.Proof.Ed25519.AArch64
end

/-!
# Ed25519 field programs: correctness of the lowering

Each arithmetic operation uses the A64 field arithmetic proof. An induction
composes these into a proof for any list of field operations.
-/

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}


open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : Addr) : Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .sqr o a => Function.update e o (e a * e a)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : Env) (o a b i : Slot) :
    evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_add_apply (e : Env) (o a b i : Slot) :
    evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : Env) (o a b i : Slot) :
    evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 64 704 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (k : Keep base t u) :
    Keep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem env_update {base : Addr} {m m' : Mem} (o : Slot)
    (h : Outside base (offset o) 32 m m') :
    env m' base = Function.update (env m base) o (F m' base (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [env]
  · rw [Function.update_of_ne hi]
    simp only [env, F]
    have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem op_keep {base : Addr} {o : Slot} {s t : State} (h : Op base (offset o) s t) :
    Keep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega)
    (by simp only [offset]; omega)⟩

/-- The slots `S` hold values below `2²⁵⁵ + 2¹³⁶`, as `fieldAdd1` and `fieldSub1` need. -/
def Small (m : Mem) (base : Addr) (S : Slot → Bool) : Prop :=
  ∀ i, S i = true → fe m base (offset i) < 2 ^ 255 + 2 ^ 136

theorem Small.none (m : Mem) (base : Addr) : Small m base fun _ => false := fun _ h => nomatch h

/-- Writing slot `o` alone, small if `b`. -/
theorem Small.update {base : Addr} {m m' : Mem} {S : Slot → Bool} {o : Slot} (h : Outside base (offset o) 32 m m')
    (hS : Small m base S) (b : Bool) (hb : b = true → fe m' base (offset o) < 2 ^ 255 + 2 ^ 136) :
    Small m' base fun i => if i = o then b else S i := by
  intro i hi
  by_cases ho : i = o
  · subst ho
    simp only [ite_true] at hi
    exact hb hi
  · simp only [ho, ite_false] at hi
    have hne : i.val ≠ o.val := fun h => ho (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
    exact hS i hi

theorem Small.mono {base : Addr} {m : Mem} {S S' : Slot → Bool} (h : ∀ i, S i = true → S' i = true)
    (hS : Small m base S') : Small m base S := fun i hi => hS i (h i hi)

/-- Writing memory outside the slots. -/
theorem Small.frame {base : Addr} {m m' : Mem} {S : Slot → Bool} {o n : Nat} (h : Outside base o n m m')
    (ho : 64 + 32 * 22 ≤ o) (hS : Small m base S) : Small m' base S := by
  intro i hi
  have := i.isLt
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
  exact hS i hi

def smallAfterOps (ops : List FieldOp) (S : Slot → Bool) : Slot → Bool :=
  ops.foldl (fun S op => op.small S) S

theorem small_mono (op : FieldOp) {C S : Slot → Bool} (h : ∀ i, C i = true → S i = true) :
    ∀ i, op.small C i = true → op.small S i = true := by
  intro i hi
  cases op <;> simp only [FieldOp.small] at hi ⊢ <;> split <;> simp_all

/-- One operation, lowered with the slots `C` known small, where the slots `S` are. -/
theorem fieldOpS_ok {s : State} {base : Addr} (hs : Scr s base large) (op : FieldOp) {C S : Slot → Bool}
    (hCS : ∀ i, C i = true → S i = true) (hS : Small s.mem base S) :
    WP isa (.block (op.codeS C)) s fun t => Keep base s t ∧ env t.mem base = evalOp op (env s.mem base) ∧
      Small t.mem base (op.small S) ∧ Outside base (offset op.out) 32 s.mem t.mem := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have hP : VG.Spec.X25519.P < 2 ^ 255 + 2 ^ 136 := by simp only [VG.Spec.X25519.P]; omega
  cases op with
  | copy o a =>
    refine WP.mono (copyField_opB hs o a) fun t ⟨h, e⟩ => ?_
    refine ⟨op_keep h, by rw [env_update o h.mem]; simp only [F]; rw [e]; rfl, ?_, h.mem⟩
    exact hS.update h.mem (S a) fun ha => by rw [e]; exact hS a ha
  | const o v =>
    refine WP.mono (constField_opB hs o v) fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl,
      hS.update h.mem true fun _ => by rw [r]; exact Nat.lt_trans v.isLt hP, h.mem⟩
  | mul o a b =>
    refine WP.mono (mul_okB hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
      (slot_rangeWith (large := large) b)) fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem true fun _ => by omega, h.mem⟩
  | sqr o a =>
    refine WP.mono (sqr_okB hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a))
      fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem true fun _ => by omega, h.mem⟩
  | add o a b =>
    show WP isa (.block (if (C a && C b) = true then fieldAdd1 (offset o) (offset a) (offset b)
      else fieldAdd (offset o) (offset a) (offset b))) s _
    split
    · next hc =>
      rw [Bool.and_eq_true] at hc
      have := hS a (hCS a hc.1)
      have := hS b (hCS b hc.2)
      refine WP.mono (add1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
        (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun, h.mem⟩
    · refine WP.mono (add_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
        (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun, h.mem⟩
  | sub o a b =>
    show WP isa (.block (if C b = true then fieldSub1 (offset o) (offset a) (offset b)
      else fieldSub (offset o) (offset a) (offset b))) s _
    split
    · next hc =>
      have := hS b (hCS b hc)
      refine WP.mono (sub1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
        (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun, h.mem⟩
    · refine WP.mono (sub_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
        (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun, h.mem⟩

/-- A field program lowered with the slots `C` known small, where the slots `S`
are: what it computes, the slots it leaves small, and that it writes only its
results' slots. -/
theorem fieldCodeFrom_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large)
    {C S : Slot → Bool} (hCS : ∀ i, C i = true → S i = true) (hS : Small s.mem base S) :
    WP isa (.block (fieldCodeFrom C ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) ∧ Small t.mem base (smallAfterOps ops S) ∧
      ∀ x, (∀ op ∈ ops, ofs base x < offset op.out ∨ offset op.out + 32 ≤ ofs base x) → t.mem x = s.mem x := by
  induction ops generalizing s C S with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, hS, fun _ _ => rfl⟩
  | cons op ops ih =>
    rw [fieldCodeFrom, WP.block_append_iff]
    refine WP.mono (fieldOpS_ok hs op hCS hS) fun t ⟨ht, et, st, ot⟩ => ?_
    refine WP.mono (ih (ht.scr hs) (small_mono op hCS) st) fun u ⟨hu, eu, su, mu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl, su, fun x hx =>
      (mu x fun o ho => hx o (List.mem_cons_of_mem _ ho)).trans (ot x (hx op List.mem_cons_self))⟩

/-- `fieldCode`, with the slots `S` small before it: the slots it leaves small. -/
theorem fieldCode_okS (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large)
    {S : Slot → Bool} (hS : Small s.mem base S) :
    WP isa (.block (fieldCode ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) ∧ Small t.mem base (smallAfterOps ops S) :=
  WP.mono (fieldCodeFrom_ok ops hs (C := fun _ => false) nofun hS) fun _ ⟨k, e, sm, _⟩ => ⟨k, e, sm⟩

theorem fieldCode_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block (fieldCode ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) :=
  WP.mono (fieldCode_okS ops hs (Small.none s.mem base)) fun _ ⟨k, e, _⟩ => ⟨k, e⟩

theorem constField_ok {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o v := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (constField_op hs o v) fun t ⟨hk, hv⟩ => ?_
  exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]⟩

theorem copyField_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o (env s.mem base a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (copyField_op hs o a) fun t ⟨hk, hv⟩ => ?_
  exact ⟨op_keep hk, by rw [env_update o hk.mem, hv]; rfl⟩

/-- `[o] := [a] · [b]²` on slots. -/
theorem sqrMulField_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) :
    WP isa (.block (fieldSqrMul (offset o) (offset a) (offset b))) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o
        (env s.mem base a * (env s.mem base b * env s.mem base b)) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (sqrMul_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
    (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
  exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) :
    point (evalOps pointAddOps e) 0 1 2 3 = addResult e 4 (by decide) := by
  rfl

/-- What `pointDoubleOps` computes: the addition formula with `p = q`, its
products of equal factors as squares. -/
def doubleResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 1 - e 0)
  let b := (e 1 + e 0) * (e 1 + e 0)
  let c := e 3 * e 3 * e 16 + e 3 * e 3 * e 16
  let dd := e 2 * e 2 + e 2 * e 2
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointDouble_formula (e : Env) :
    point (evalOps pointDoubleOps e) 0 1 2 3 = doubleResult e := by
  rfl

theorem doubleResult_eq (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    doubleResult e = Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) := by
  simp only [doubleResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem addResult_eq (e : Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    addResult e q hq = Spec.Ed25519.pointAdd (point e 0 1 2 3)
      (point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) :=
  (pointAdd_formula e).trans (addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) :=
  (pointDouble_formula e).trans (doubleResult_eq e hd)

end VG.Proof.Ed25519.AArch64
