module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # `add_twice4`

The sum of the field elements at `a` and `b` into `o`, with its carry out of
bit 256 folded back as 38 (`2²⁵⁶ = 2·p + 38`). All of its loads come before
its stores, so `o` may overlap `a` and `b` in any way. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

/-- The loads and the four-word sum. -/
abbrev addChain (a b : Nat) : List Instr :=
  [.ldp .x3 .x4 .x0 a, .ldp .x7 .x8 .x0 b, .adds .x .x3 .x3 .x7, .adcs .x .x4 .x4 .x8,
    .ldp .x5 .x6 .x0 (a + 16), .ldp .x7 .x8 .x0 (b + 16), .adcs .x .x5 .x5 .x7,
    .adcs .x .x6 .x6 .x8]

/-- The carry folded back as 38. -/
abbrev addFold : List Instr :=
  [.movz .w .x9 38 0, .cselc .x .x9 .x9 .x17 .hs, .adds .x .x3 .x3 .x9,
    .adcs .x .x4 .x4 .x17, .adcs .x .x5 .x5 .x17, .adc .x .x6 .x6 .x17]

/-- x3–x6 into the field element at `o`. -/
abbrev store36 (o : Nat) : List Instr := [.stp .x3 .x4 .x0 o, .stp .x5 .x6 .x0 (o + 16)]

theorem addTwice4_eq (o a b : Nat) :
    Impl.X25519.AArch64.Alt.addTwice4 o a b = addChain a b ++ (addFold ++ store36 o) := rfl

theorem addChain_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : AltRange a large) (hb : AltRange b large) :
    WP isa (.block (addChain a b)) s fun t =>
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) + 2 ^ 256 * t.c.toNat =
        fe s.mem base a + fe s.mem base b ∧ Keeps [.x3, .x4, .x5, .x6, .x7, .x8] s t := by
  have _hcap := workSize_le large
  obtain ⟨aa, ab, ac⟩ := ha
  obtain ⟨ba, bb, bc⟩ := hb
  have a16 : (a + 16) % 8 = 0 := by omega
  have b16 : (b + 16) % 8 = 0 := by omega
  have w3 : Reg.x3 ≠ .x0 := by decide
  have w4 : Reg.x4 ≠ .x0 := by decide
  have w5 : Reg.x5 ≠ .x0 := by decide
  have w6 : Reg.x6 ≠ .x0 := by decide
  have w7 : Reg.x7 ≠ .x0 := by decide
  have w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs aa (by omega) (by omega) (by decide : Reg.x3 ≠ .x4),
    ldp_sc ((hs.write w3 _).write w4 _) ba (by omega) (by omega) (by decide : Reg.x7 ≠ .x8),
    ldp_sc (((((hs.write w3 _).write w4 _).write w7 _).write w8 _).awc w3 _ _ _ |>.awc w4 _ _ _)
      a16 (by omega) (by omega) (by decide : Reg.x5 ≠ .x6),
    ldp_sc ((((((((hs.write w3 _).write w4 _).write w7 _).write w8 _).awc w3 _ _ _).awc w4 _ _ _).write
      w5 _).write w6 _) b16 (by omega) (by omega) (by decide : Reg.x7 ≠ .x8),
    exec_adds_x, exec_adcs_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry, RegUpd.gpr_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write, reduceCtorEq,
    ite_true, ite_false, BitVec.setWidth_eq]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := add4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    rw [show a + 16 + 8 = a + 24 by omega, show b + 16 + 8 = b + 24 by omega]
    dsimp only [fe, addCarry, carryOut, Size.bits] at h ⊢
    rw [Bool.toNat_false, Nat.add_zero] at h
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem addFold_ok (s : State) (hz : s.gpr .x17 = 0)
    (hb : val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) + 38 * s.c.toNat < 2 ^ 256) :
    WP isa (.block addFold) s fun t =>
      val4 (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) =
        val4 (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) + 38 * s.c.toNat ∧
      Keeps [.x3, .x4, .x5, .x6, .x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_w, exec_cselc_x, exec_adds_x,
    exec_adcs_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    CondCode.holds, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hz]
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have hv : (if s.c = true then BitVec.setWidth 64 (BitVec.setWidth 32 (38 : BitVec 16)) else
        (0 : BitVec 64)).toNat = 38 * s.c.toNat := by
      cases s.c <;> rfl
    generalize (if s.c = true then BitVec.setWidth 64 (BitVec.setWidth 32 (38 : BitVec 16)) else
      (0 : BitVec 64)) = v at hv ⊢
    have e0 := addCarry_value (s.gpr .x3) v false
    have e1 := addCarry_value (s.gpr .x4) 0 (carryOut (s.gpr .x3) v false)
    have e2 := addCarry_value (s.gpr .x5) 0 (carryOut (s.gpr .x4) 0 (carryOut (s.gpr .x3) v false))
    have e3 := addCarry_value (s.gpr .x6) 0 (carryOut (s.gpr .x5) 0
      (carryOut (s.gpr .x4) 0 (carryOut (s.gpr .x3) v false)))
    dsimp only [addCarry, carryOut, Size.bits] at e0 e1 e2 e3 ⊢
    have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [val4, Bool.toNat_false, Nat.add_zero, z] at e0 e1 e2 e3 hb ⊢
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `[o] := [a] + [b]`, less `2²⁵⁶ − 38` once if the sum carries out of bit
256, for operands that sum below `2²⁵⁷ − 38`. -/
theorem addTwice4_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : AltRange o large) (ha : AltRange a large) (hb : AltRange b large)
    (hz : s.gpr .x17 = 0) (hsum : fe s.mem base a + fe s.mem base b < 2 ^ 257 - 38) :
    WP isa (.block (Impl.X25519.AArch64.Alt.addTwice4 o a b)) s fun t =>
      AltOp base o s t ∧ ∃ k ≤ 1, fe t.mem base o + (2 ^ 256 - 38) * k =
        fe s.mem base a + fe s.mem base b := by
  have _hcap := workSize_le large
  rw [addTwice4_eq, WP.block_append_iff]
  refine WP.mono (addChain_ok hs ha hb) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hc := Bool.toNat_le s₁.c
  have _hv := val4_lt (s₁.gpr .x3) (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6)
  refine WP.mono (addFold_ok s₁ ((k1.gpr _ (by decide)).trans hz) (by omega))
    fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho.1 ho.2.1 ho.2.2 .x3 .x4 .x5 .x6) fun t ht => ?_
  subst t
  have m2 : s₂.mem = s.mem := by rw [k2.mem, k1.mem]
  have _ho := ho.2.2
  refine ⟨⟨fun r hr => ?_, by rw [rd_withMem, k2.rd, k1.rd], by rw [wr_withMem, k2.wr, k1.wr],
    by rw [sp_withMem, k2.sp, k1.sp], ?_⟩, s₁.c.toNat, hc, ?_⟩
  · simp only [altClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_withMem, k2.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true]), k1.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, hr,
      not_false_eq_true])]
  · rw [mem_withMem, ← m2]
    exact st4_outside _ _ (by omega) _ _ _ _
  · rw [mem_withMem, fe_st4 _ _ (by omega), e2]
    omega

end VG.Proof.X25519.AArch64.Alt
