module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # `cmadd_4`

`c · a + b` for the word `c` in x1 and the field elements at `a` and `b`,
into `o`, below `2·p`: the five-word sum folded once at bit 255 (as 19). Its
loads of `a` come before its stores and those of `b` too, so `o` may overlap
`a` and `b` in any way. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

/-- The loads of `a` and its product by x1, into x3–x6 and x10. -/
abbrev cmRow (a : Nat) : List Instr :=
  [.ldp .x7 .x8 .x0 a, .ldp .x9 .x10 .x0 (a + 16),
    .mul .x .x3 .x1 .x7, .mul .x .x4 .x1 .x8, .mul .x .x5 .x1 .x9, .mul .x .x6 .x1 .x10,
    .umulh .x7 .x1 .x7, .umulh .x8 .x1 .x8, .umulh .x9 .x1 .x9, .umulh .x10 .x1 .x10,
    .adds .x .x4 .x4 .x7, .adcs .x .x5 .x5 .x8, .adcs .x .x6 .x6 .x9, .adc .x .x10 .x10 .x17]

/-- The field element at `b` added to x3–x6 and x10. -/
abbrev cmAdd (b : Nat) : List Instr :=
  [.ldp .x7 .x8 .x0 b, .adds .x .x3 .x3 .x7, .adcs .x .x4 .x4 .x8,
    .ldp .x7 .x8 .x0 (b + 16), .adcs .x .x5 .x5 .x7, .adcs .x .x6 .x6 .x8,
    .adc .x .x10 .x10 .x17]

/-- The five words x3–x6, x10 folded at bit 255. -/
abbrev cmFold : List Instr :=
  [.adds .x .x7 .x6 .x6, .lsr .x .x6 .x7 1, .adc .x .x8 .x10 .x10, .movz .w .x9 19 0,
    .mul .x .x7 .x8 .x9, .adds .x .x3 .x3 .x7, .adcs .x .x4 .x4 .x17,
    .adcs .x .x5 .x5 .x17, .adc .x .x6 .x6 .x17]

theorem cmadd4_eq (o a b : Nat) :
    Impl.X25519.AArch64.Alt.cmadd4 o a b =
      cmRow a ++ (cmAdd b ++ (cmFold ++
        ([.stp .x3 .x4 .x0 o, .stp .x5 .x6 .x0 (o + 16)] : List Instr))) := rfl

theorem cmRow_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat}
    (ha : AltRange a large) (hz : s.gpr .x17 = 0) :
    WP isa (.block (cmRow a)) s fun t =>
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) + 2 ^ 256 * (t.gpr .x10).toNat =
        (s.gpr .x1).toNat * fe s.mem base a ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10] s t := by
  have _hcap := workSize_le large
  obtain ⟨aa, ab, ac⟩ := ha
  have a16 : (a + 16) % 8 = 0 := by omega
  have w7 : Reg.x7 ≠ .x0 := by decide
  have w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs aa (by omega) (by omega) (by decide : Reg.x7 ≠ .x8),
    ldp_sc ((hs.write w7 _).write w8 _) a16 (by omega) (by omega) (by decide : Reg.x9 ≠ .x10),
    exec_mul_x, exec_umulh_x, exec_adds_x, exec_adcs_x, exec_adc_x,
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := rowFirst_value (s.gpr .x1) (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
    rw [show a + 16 + 8 = a + 24 by omega]
    dsimp only [fe, addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem cmAdd_ok {s : State} {base : Addr} (hs : Scr s base large) {b : Nat}
    (hb : AltRange b large) (hz : s.gpr .x17 = 0)
    (hlt : val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) + 2 ^ 256 * (s.gpr .x10).toNat +
      fe s.mem base b < 2 ^ 320) :
    WP isa (.block (cmAdd b)) s fun t =>
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) + 2 ^ 256 * (t.gpr .x10).toNat =
        val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) + 2 ^ 256 * (s.gpr .x10).toNat +
          fe s.mem base b ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x8, .x10] s t := by
  have _hcap := workSize_le large
  obtain ⟨ba, bb, bc⟩ := hb
  have b16 : (b + 16) % 8 = 0 := by omega
  have w3 : Reg.x3 ≠ .x0 := by decide
  have w4 : Reg.x4 ≠ .x0 := by decide
  have w7 : Reg.x7 ≠ .x0 := by decide
  have w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs ba (by omega) (by omega) (by decide : Reg.x7 ≠ .x8),
    ldp_sc ((((hs.write w7 _).write w8 _).awc w3 _ _ _).awc w4 _ _ _) b16 (by omega) (by omega)
      (by decide : Reg.x7 ≠ .x8),
    exec_adds_x, exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_addWithCarry, RegUpd.c_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := add4_value (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    have e := addCarry_value (s.gpr .x10) 0 (carryOut (s.gpr .x6) (word s.mem base (b + 24))
      (carryOut (s.gpr .x5) (word s.mem base (b + 16)) (carryOut (s.gpr .x4) (word s.mem base (b + 8))
        (carryOut (s.gpr .x3) (word s.mem base b) false))))
    have hl := val4_lt (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
    have hx := (addCarry (s.gpr .x10) 0 (carryOut (s.gpr .x6) (word s.mem base (b + 24))
      (carryOut (s.gpr .x5) (word s.mem base (b + 16)) (carryOut (s.gpr .x4) (word s.mem base (b + 8))
        (carryOut (s.gpr .x3) (word s.mem base b) false))))).isLt
    rw [show b + 16 + 8 = b + 24 by omega]
    dsimp only [fe, addCarry, carryOut, Size.bits] at h e hx hlt ⊢
    have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [Bool.toNat_false, Nat.add_zero, z] at h e hx ⊢
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem fold_hi (x6 x10 : Word) (h : x10.toNat < 2 ^ 58) :
    ((x10 + x10 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x6.toNat + x6.toNat + false.toNat)).toNat) *
      BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16))).toNat =
      19 * (2 * x10.toNat + x6.toNat / 2 ^ 63) := by
  have := x6.isLt
  have e : BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16)) = 19 := rfl
  rw [e, fold_c]
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : x6.toNat / 2 ^ 63 ≤ 1 := by omega
  have e19 : (19 : BitVec 64).toNat = 19 := rfl
  rw [e19]
  omega

theorem cmFold_ok (s : State) (hz : s.gpr .x17 = 0)
    (hq : 19 * (val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) +
      2 ^ 256 * (s.gpr .x10).toNat) < 2 ^ 316) :
    WP isa (.block cmFold) s fun t => ∃ q,
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) + (2 ^ 255 - 19) * q =
        val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) + 2 ^ 256 * (s.gpr .x10).toNat ∧
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) < 2 ^ 256 - 38 ∧
      Keeps [.x3, .x4, .x5, .x6, .x7, .x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_adds_x, exec_lsr1_x, exec_adc_x,
    exec_movz_w, exec_mul_x, exec_adcs_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  dsimp only [Size.bits]
  have hx10 : (s.gpr .x10).toNat < 2 ^ 58 := by omega
  have h := add4_value (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
    ((s.gpr .x6 + s.gpr .x6 + BitVec.ofNat 64 false.toNat) >>> 1)
    ((s.gpr .x10 + s.gpr .x10 +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (s.gpr .x6).toNat + (s.gpr .x6).toNat + false.toNat)).toNat) *
      BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16))) 0 0 0 false
  dsimp only [addCarry, carryOut] at h
  have hU := fold_lo (s.gpr .x6)
  have hM := fold_hi (s.gpr .x6) (s.gpr .x10) hx10
  have z : (0 : BitVec 64).toNat = 0 := rfl
  have := (s.gpr .x3).isLt
  have := (s.gpr .x4).isLt
  have := (s.gpr .x5).isLt
  have := (s.gpr .x6).isLt
  simp only [val4, z, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h hq hU hM ⊢
  refine ⟨2 * (s.gpr .x10).toNat + (s.gpr .x6).toNat / 2 ^ 63, ?_, ?_,
    ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · omega
  · omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- `[o] := c · [a] + [b]` for the word `c` in x1, modulo `p` and below `2·p`,
for `19 (c · [a] + [b]) < 2³¹⁶`. -/
theorem cmadd4_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : AltRange o large) (ha : AltRange a large) (hb : AltRange b large)
    (hz : s.gpr .x17 = 0)
    (hlt : 19 * ((s.gpr .x1).toNat * fe s.mem base a + fe s.mem base b) < 2 ^ 316) :
    WP isa (.block (Impl.X25519.AArch64.Alt.cmadd4 o a b)) s fun t =>
      AltOp base o s t ∧ fe t.mem base o < 2 ^ 256 - 38 ∧ ∃ q, fe t.mem base o + (2 ^ 255 - 19) * q =
        (s.gpr .x1).toNat * fe s.mem base a + fe s.mem base b := by
  have _hcap := workSize_le large
  rw [cmadd4_eq, WP.block_append_iff]
  refine WP.mono (cmRow_ok hs ha hz) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 : s₁.gpr .x17 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (cmAdd_ok hs₁ hb hz1 (by rw [e1, k1.mem]; omega)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmFold_ok s₂ ((k2.gpr _ (by decide)).trans hz1) (by rw [e2, e1, k1.mem]; omega))
    fun s₃ ⟨q, e3, l3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho.1 ho.2.1 ho.2.2 .x3 .x4 .x5 .x6) fun t ht => ?_
  subst t
  have m3 : s₃.mem = s.mem := by rw [k3.mem, k2.mem, k1.mem]
  have _ho := ho.2.2
  have hf := fe_st4 s₃.mem base (o := o) (by omega) (s₃.gpr .x3) (s₃.gpr .x4) (s₃.gpr .x5)
    (s₃.gpr .x6)
  refine ⟨⟨fun r hr => ?_, by rw [rd_withMem, k3.rd, k2.rd, k1.rd],
    by rw [wr_withMem, k3.wr, k2.wr, k1.wr], by rw [sp_withMem, k3.sp, k2.sp, k1.sp], ?_⟩,
    by rw [mem_withMem, hf]; exact l3, q, ?_⟩
  · simp only [altClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_withMem, k3.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k2.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k1.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true])]
  · rw [mem_withMem, ← m3]
    exact st4_outside _ _ (by omega) _ _ _ _
  · rw [mem_withMem, hf, e3, e2, e1, k1.mem]

end VG.Proof.X25519.AArch64.Alt
