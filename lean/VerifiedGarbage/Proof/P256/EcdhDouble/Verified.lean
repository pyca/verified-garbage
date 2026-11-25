module

public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.EcdhJac.State
public import VerifiedGarbage.Proof.P256.VerifySparse.Arithmetic
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall

/-! The doubling's two operations of its own, `3x` and `x/2`, its raw program and the allocated one. -/

@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519
open VG.Proof.P256.VerifySparse (p four masked_words)
open VG.Impl.P256.EcdhDouble

/-! ### Words -/

private theorem words (s : State) : regsVal s (low 4) =
    four (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) := rfl

private theorem add4_ok (s : State) (y0 y1 y2 y3 : Reg) (h1 : y1 ≠ .x8) (h2 : y2 ∉ [Reg.x8, .x9])
    (h3 : y3 ∉ [Reg.x8, .x9, .x10]) :
    WP isa (.block [.adds .x .x8 .x8 y0, .adcs .x .x9 .x9 y1, .adcs .x .x10 .x10 y2,
      .adcs .x .x11 .x11 y3]) s fun t =>
      regsVal t (low 4) + 2 ^ 256 * t.c.toNat = regsVal s (low 4) +
        four (s.gpr y0) (s.gpr y1) (s.gpr y2) (s.gpr y3) ∧ Keeps [.x8, .x9, .x10, .x11] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2 h3
  rw [show ([.adds .x .x8 .x8 y0, .adcs .x .x9 .x9 y1, .adcs .x .x10 .x10 y2, .adcs .x .x11 .x11 y3] : List Instr) =
    [.adds .x .x8 .x8 y0] ++ ([.adcs .x .x9 .x9 y1] ++ ([.adcs .x .x10 .x10 y2] ++ [.adcs .x .x11 .x11 y3])) from rfl,
    WP.block_append_iff]
  refine WP.mono (addc_ok s .x8 .x8 y0 true (c := false) rfl) fun s1 ⟨e1, c1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s1 .x9 .x9 y1 false (c := s1.c) rfl) fun s2 ⟨e2, c2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s2 .x10 .x10 y2 false (c := s2.c) rfl) fun s3 ⟨e3, c3, k3⟩ => ?_
  refine WP.mono (addc_ok s3 .x11 .x11 y3 false (c := s3.c) rfl) fun t ⟨e4, c4, k4⟩ => ?_
  rw [k1.gpr _ (by decide), k1.gpr _ (by simpa using h1), c1] at e2 c2
  rw [k2.gpr _ (by decide), k1.gpr _ (by decide), k2.gpr _ (by simpa using h2.2), k1.gpr _ (by simpa using h2.1), c2] at e3 c3
  rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
    k3.gpr _ (by simpa using h3.2.2), k2.gpr _ (by simpa using h3.2.1), k1.gpr _ (by simpa using h3.1), c3] at e4 c4
  refine ⟨?_, (((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  rw [words, words, c4, e4, k4.gpr .x10 (by decide), e3, k4.gpr .x9 (by decide), k3.gpr .x9 (by decide), e2,
    k4.gpr .x8 (by decide), k3.gpr .x8 (by decide), k2.gpr .x8 (by decide), e1]
  have v0 := Word64.addCarry_value (s.gpr .x8) (s.gpr y0) false
  have v1 := Word64.addCarry_value (s.gpr .x9) (s.gpr y1) (Word64.carryOut (s.gpr .x8) (s.gpr y0) false)
  have v2 := Word64.addCarry_value (s.gpr .x10) (s.gpr y2)
    (Word64.carryOut (s.gpr .x9) (s.gpr y1) (Word64.carryOut (s.gpr .x8) (s.gpr y0) false))
  have v3 := Word64.addCarry_value (s.gpr .x11) (s.gpr y3) (Word64.carryOut (s.gpr .x10) (s.gpr y2)
    (Word64.carryOut (s.gpr .x9) (s.gpr y1) (Word64.carryOut (s.gpr .x8) (s.gpr y0) false)))
  simp only [Bool.toNat_false, Nat.add_zero] at v0
  unfold four
  omega_using [v0, v1, v2, v3]

private theorem sub4_ok (s : State) (y0 y1 y2 y3 : Reg) (h1 : y1 ≠ .x8) (h2 : y2 ∉ [Reg.x8, .x9])
    (h3 : y3 ∉ [Reg.x8, .x9, .x10]) :
    WP isa (.block [.subs .x .x8 .x8 y0, .sbcs .x .x9 .x9 y1, .sbcs .x .x10 .x10 y2,
      .sbcs .x .x11 .x11 y3]) s fun t =>
      regsVal t (low 4) + four (s.gpr y0) (s.gpr y1) (s.gpr y2) (s.gpr y3) =
        regsVal s (low 4) + 2 ^ 256 * (!t.c).toNat ∧ Keeps [.x8, .x9, .x10, .x11] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2 h3
  rw [show ([.subs .x .x8 .x8 y0, .sbcs .x .x9 .x9 y1, .sbcs .x .x10 .x10 y2, .sbcs .x .x11 .x11 y3] : List Instr) =
    [.subs .x .x8 .x8 y0] ++ ([.sbcs .x .x9 .x9 y1] ++ ([.sbcs .x .x10 .x10 y2] ++ [.sbcs .x .x11 .x11 y3])) from rfl,
    WP.block_append_iff]
  refine WP.mono (subc_ok s .x8 .x8 y0 true (c := true) rfl) fun s1 ⟨e1, c1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok s1 .x9 .x9 y1 false (c := s1.c) rfl) fun s2 ⟨e2, c2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok s2 .x10 .x10 y2 false (c := s2.c) rfl) fun s3 ⟨e3, c3, k3⟩ => ?_
  refine WP.mono (subc_ok s3 .x11 .x11 y3 false (c := s3.c) rfl) fun t ⟨e4, c4, k4⟩ => ?_
  rw [k1.gpr _ (by decide), k1.gpr _ (by simpa using h1), c1] at e2 c2
  rw [k2.gpr _ (by decide), k1.gpr _ (by decide), k2.gpr _ (by simpa using h2.2), k1.gpr _ (by simpa using h2.1), c2] at e3 c3
  rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
    k3.gpr _ (by simpa using h3.2.2), k2.gpr _ (by simpa using h3.2.1), k1.gpr _ (by simpa using h3.1), c3] at e4 c4
  refine ⟨?_, (((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  rw [words, words, c4, e4, k4.gpr .x10 (by decide), e3, k4.gpr .x9 (by decide), k3.gpr .x9 (by decide), e2,
    k4.gpr .x8 (by decide), k3.gpr .x8 (by decide), k2.gpr .x8 (by decide), e1]
  have v := Word64.sub4_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr y0) (s.gpr y1) (s.gpr y2)
    (s.gpr y3) true
  have nt (b : Bool) : (!b).toNat = 1 - b.toNat := by cases b <;> rfl
  rw [nt]
  simp only [Word64.val4, Bool.toNat_true] at v
  unfold four
  omega_using [v]

/-- The word `k` bits up a pair of words. -/
private theorem extr_toNat (hi lo : BitVec 64) (k : Nat) :
    ((hi ++ lo).extractLsb' k 64).toNat = (2 ^ 64 * hi.toNat + lo.toNat) / 2 ^ k % 2 ^ 64 := by
  have e : (hi ++ lo).toNat = 2 ^ 64 * hi.toNat + lo.toNat := by
    rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt lo.isLt]
  rw [BitVec.extractLsb'_toNat, e, Nat.shiftRight_eq_div_pow]

/-! ### The prime under a mask -/

private theorem addPrime_ok (s : State) (b : Bool) (hz : s.gpr .x7 = 0) (hm : s.gpr .x17 = if b then -1 else 0) :
    WP isa (.block addPrime) s fun t =>
      regsVal t (low 4) + 2 ^ 256 * t.c.toNat = regsVal s (low 4) + (if b then p else 0) ∧
      Keeps [.x1, .x2, .x8, .x9, .x10, .x11] s t := by
  rw [show addPrime = ([.lsr .x .x1 .x17 32, .lsl .x .x2 .x17 32, .sub .x .x2 .x2 .x17] : List Instr) ++
    [.adds .x .x8 .x8 .x17, .adcs .x .x9 .x9 .x1, .adcs .x .x10 .x10 .x7, .adcs .x .x11 .x11 .x2] from rfl,
    WP.block_append_iff]
  have first : WP isa (.block [.lsr .x .x1 .x17 32, .lsl .x .x2 .x17 32, .sub .x .x2 .x2 .x17]) s fun t =>
      t.gpr .x1 = s.gpr .x17 >>> 32 ∧ t.gpr .x2 = (s.gpr .x17 <<< 32) - s.gpr .x17 ∧ Keeps [.x1, .x2] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 32 < 64 by decide, ite_true,
      RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  refine WP.mono first fun s1 ⟨e1, e2, k1⟩ => ?_
  refine WP.mono (add4_ok s1 .x17 .x1 .x7 .x2 (by decide) (by decide) (by decide)) fun t ⟨et, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))⟩
  rw [et, words, words, e1, e2, k1.gpr .x17 (by decide), k1.gpr .x7 (by decide), k1.gpr .x8 (by decide),
    k1.gpr .x9 (by decide), k1.gpr .x10 (by decide), k1.gpr .x11 (by decide), hz, hm, (masked_words b).2.2]

/-! ### Times three -/

private theorem shl1 (x : BitVec 64) : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem tripleSum_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block tripleSum) s fun t =>
      regsVal t (low 4) + 2 ^ 256 * (t.gpr .x16).toNat = 3 * regsVal s (low 4) ∧
      Keeps [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16] s t := by
  rw [show tripleSum = ([.lsl .x .x12 .x8 1, .extr .x .x13 .x9 .x8 63, .extr .x .x14 .x10 .x9 63,
      .extr .x .x15 .x11 .x10 63, .lsr .x .x16 .x11 63] : List Instr) ++
    (([.adds .x .x8 .x8 .x12, .adcs .x .x9 .x9 .x13, .adcs .x .x10 .x10 .x14, .adcs .x .x11 .x11 .x15] : List Instr) ++
      [.adc .x .x16 .x16 .x7]) from rfl, WP.block_append_iff]
  have first : WP isa (.block [.lsl .x .x12 .x8 1, .extr .x .x13 .x9 .x8 63, .extr .x .x14 .x10 .x9 63,
      .extr .x .x15 .x11 .x10 63, .lsr .x .x16 .x11 63]) s fun t =>
      four (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) + 2 ^ 256 * (t.gpr .x16).toNat =
        2 * regsVal s (low 4) ∧ Keeps [.x12, .x13, .x14, .x15, .x16] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 1 < 64 by decide,
      show 63 < 64 by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [words]
      unfold four
      rw [shl1, extr_toNat, extr_toNat, extr_toNat,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have h0 := (s.gpr .x8).isLt
      have h1 := (s.gpr .x9).isLt
      have h2 := (s.gpr .x10).isLt
      have h3 := (s.gpr .x11).isLt
      omega_using [h0, h1, h2, h3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  refine WP.mono first fun s1 ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add4_ok s1 .x12 .x13 .x14 .x15 (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  have last : WP isa (.block [.adc .x .x16 .x16 .x7]) s2 fun t =>
      t.gpr .x16 = Word64.addCarry (s2.gpr .x16) (s2.gpr .x7) s2.c ∧ Keeps [.x16] s2 t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono last fun t ⟨et, k3⟩ =>
    ⟨?_, ((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans (k3.mono (by sub_regs))⟩
  have v := Word64.addCarry_value (s2.gpr .x16) (s2.gpr .x7) s2.c
  have lt := (Word64.addCarry (s2.gpr .x16) (s2.gpr .x7) s2.c).isLt
  have z2 : (s2.gpr .x7).toNat = 0 := by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hz]; rfl
  have e16 : s2.gpr .x16 = s1.gpr .x16 := k2.gpr _ (by decide)
  have c2 := Bool.toNat_le s2.c
  have bound : (s1.gpr .x16).toNat ≤ 1 := by
    have l := regsVal_lt s (low 4)
    change regsVal s (low 4) < 2 ^ 256 at l
    omega_using [e1, l]
  have er : regsVal s1 (low 4) = regsVal s (low 4) := regsVal_congr fun q hq =>
    k1.gpr q ((by decide : ∀ q ∈ low 4, q ∉ [Reg.x12, .x13, .x14, .x15, .x16]) q hq)
  have et' : regsVal t (low 4) = regsVal s2 (low 4) := regsVal_congr fun q hq =>
    k3.gpr q ((by decide : ∀ q ∈ low 4, q ∉ [Reg.x16]) q hq)
  rw [er] at e2
  rw [et', et]
  rw [e16, z2] at v
  rw [e16] at lt ⊢
  omega_using [e1, e2, v, lt, bound, c2]

/-- `q p` without its top word, for a small positive `q`. -/
private theorem qp_words (q : Nat) (h : 1 ≤ q) (h' : q ≤ 3) :
    four (0 - BitVec.ofNat 64 q) (BitVec.ofNat 64 q <<< 32 - 1) 0
      (BitVec.ofNat 64 q - BitVec.ofNat 64 q <<< 32) + 2 ^ 256 * (q - 1) = q * p :=
  (by decide +kernel : ∀ q < 4, 1 ≤ q → four (0 - BitVec.ofNat 64 q) (BitVec.ofNat 64 q <<< 32 - 1) 0
      (BitVec.ofNat 64 q - BitVec.ofNat 64 q <<< 32) + 2 ^ 256 * (q - 1) = q * p) q (by omega_using [h']) h

private theorem tripleReduce_ok (s : State) {T : Nat} (hz : s.gpr .x7 = 0) (hT : T < 3 * p)
    (hs : regsVal s (low 4) + 2 ^ 256 * (s.gpr .x16).toNat = T) :
    WP isa (.block tripleReduce) s fun t => ∃ b : Bool,
      regsVal t (low 4) + ((s.gpr .x16).toNat + 1) * p = T + 2 ^ 256 * b.toNat ∧
      t.gpr .x17 = (if b then -1 else 0) ∧
      Keeps [.x2, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17] s t := by
  rw [show tripleReduce = ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .sub .x .x12 .x7 .x16, .lsl .x .x13 .x16 32,
      .sub .x .x15 .x16 .x13, .sub .x .x13 .x13 .x2] : List Instr) ++
    (([.subs .x .x8 .x8 .x12, .sbcs .x .x9 .x9 .x13, .sbcs .x .x10 .x10 .x7, .sbcs .x .x11 .x11 .x15] : List Instr) ++
      [.sbc .x .x17 .x7 .x7]) from rfl, WP.block_append_iff]
  have first : WP isa (.block [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .sub .x .x12 .x7 .x16, .lsl .x .x13 .x16 32,
      .sub .x .x15 .x16 .x13, .sub .x .x13 .x13 .x2]) s fun t =>
      t.gpr .x12 = 0 - (s.gpr .x16 + 1#64) ∧ t.gpr .x13 = ((s.gpr .x16 + 1#64) <<< 32) - 1 ∧
      t.gpr .x15 = (s.gpr .x16 + 1#64) - ((s.gpr .x16 + 1#64) <<< 32) ∧ Keeps [.x2, .x12, .x13, .x15, .x16] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 16 * 0 < 64 by decide,
      show 32 < 64 by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, hz,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  refine WP.mono first fun s1 ⟨e12, e13, e15, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sub4_ok s1 .x12 .x13 .x7 .x15 (by decide) (by decide) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.mono (sbcMask_ok s2 (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hz])) fun t ⟨e17, k3⟩ =>
    ⟨!s2.c, ?_, e17, ((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans (k3.mono (by sub_regs))⟩
  have er : regsVal s1 (low 4) = regsVal s (low 4) := regsVal_congr fun q hq =>
    k1.gpr q ((by decide : ∀ q ∈ low 4, q ∉ [Reg.x2, .x12, .x13, .x15, .x16]) q hq)
  have et : regsVal t (low 4) = regsVal s2 (low 4) := regsVal_congr fun q hq =>
    k3.gpr q ((by decide : ∀ q ∈ low 4, q ∉ [Reg.x17]) q hq)
  have h16 : (s.gpr .x16).toNat ≤ 2 := by
    have : 3 * p < 2 ^ 256 * 3 := by decide
    omega_using [hs, hT, this]
  have qe : s.gpr .x16 + 1#64 = BitVec.ofNat 64 ((s.gpr .x16).toNat + 1) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have w := qp_words ((s.gpr .x16).toNat + 1) (by omega_using []) (by omega_using [h16])
  rw [e12, e13, e15, k1.gpr .x7 (by decide), hz, qe, er] at e2
  rw [et]
  rw [Nat.add_sub_cancel] at w
  omega_using [e2, w, hs]

/-- The sum, the estimate of its quotient and the one correction. -/
private theorem triple_arith {x q r b : Nat} (hb : b ≤ 1) (hq : q ≤ 2)
    (hlo : 2 ^ 256 * q ≤ 3 * x) (hhi : 3 * x < 2 ^ 256 * (q + 1)) (hr : r < 2 ^ 256)
    (e : r + (q + 1) * p = 3 * x + 2 ^ 256 * b) :
    (r + (if b = 1 then p else 0)) % 2 ^ 256 = 3 * x % p := by
  have hp : p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := rfl
  rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl
  · simp only [Nat.zero_ne_one, ite_false, Nat.add_zero, Nat.mod_eq_of_lt hr]
    have lt : r < p := by
      rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl <;> omega_using [e, hhi, hp]
    rw [show 3 * x = r + p * (q + 1) by rw [Nat.mul_comm p]; omega_using [e], Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt lt]
  · simp only [ite_true]
    have h : r + p = 2 ^ 256 + (3 * x - q * p) ∧ q * p ≤ 3 * x ∧ 3 * x - q * p < p := by
      rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl <;>
        omega_using [e, hlo, hhi, hp, hr]
    generalize hd : 3 * x - q * p = d at h
    rw [h.1, Nat.add_mod_left, Nat.mod_eq_of_lt (Nat.lt_trans h.2.2 (by decide)),
      show 3 * x = d + p * q by rw [Nat.mul_comm p]; omega_using [h.2.1, hd], Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt h.2.2]

theorem triple_ok {s : State} {base : Addr} {size o a : Nat} (hs : Scr s base size)
    (ho : o + 32 ≤ size) (ha : a + 32 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hA : wordsVal s.mem base a 4 < p) :
    WP isa (.block (triple o a)) s fun t =>
      OpKeep Impl.P256.VerifySparse.M base o s t ∧
      wordsVal t.mem base o 4 = 3 * wordsVal s.mem base a 4 % p := by
  obtain hf : Fresh (low 4) := by unfold Fresh; decide
  rw [triple, show zero7 :: loads (low 4) a = [zero7] ++ loads (low 4) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s0 ⟨z0, k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) (hs.of_keeps k0 (by decide)) (a := a) ha ha8 hf) fun s1 ⟨e1, k1, _⟩ => ?_
  have z1 : s1.gpr .x7 = 0 := by rw [k1.gpr _ (by decide), z0]
  change regsVal s1 (low 4) = wordsVal s0.mem base a 4 at e1
  rw [k0.mem] at e1
  rw [WP.block_append_iff]
  refine WP.mono (tripleSum_ok s1 z1) fun s2 ⟨e2, k2⟩ => ?_
  have z2 : s2.gpr .x7 = 0 := by rw [k2.gpr _ (by decide), z1]
  rw [WP.block_append_iff]
  refine WP.mono (tripleReduce_ok s2 z2 (by rw [e1]; omega_using [hA]) e2) fun s3 ⟨b, e3, m3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addPrime_ok s3 b (by rw [k3.gpr _ (by decide), z2]) m3) fun s4 ⟨e4, k4⟩ => ?_
  have keep : Keeps (clob 4) s s4 := (((k0.mono (by decide)).trans (k1.mono (by decide))).trans
    (k2.mono (by decide))).trans ((k3.mono (by decide)).trans (k4.mono (by decide)))
  refine WP.mono (stores_ok (low 4) (hs.of_keeps keep (by decide)) (o := o) ho ho8 hf.1) fun t ⟨et, kt, ot⟩ => ?_
  refine ⟨⟨fun r hr => (kt.gpr r (by simp)).trans (keep.gpr r hr), kt.rd.trans keep.rd, kt.wr.trans keep.wr,
    kt.sp.trans keep.sp, fun x hx _ => (ot x hx).trans (congrFun keep.mem x)⟩, ?_⟩
  change wordsVal t.mem base o 4 = regsVal s4 (low 4) at et
  have l2 := regsVal_lt s2 (low 4)
  have l3 := regsVal_lt s3 (low 4)
  have l4 := regsVal_lt s4 (low 4)
  change regsVal s2 (low 4) < 2 ^ 256 at l2
  change regsVal s3 (low 4) < 2 ^ 256 at l3
  change regsVal s4 (low 4) < 2 ^ 256 at l4
  have hp : p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := rfl
  rw [e1] at e2 e3
  rw [et, ← triple_arith (Bool.toNat_le b) (q := (s2.gpr .x16).toNat) (by omega_using [e2, hA, hp])
    (by omega_using [e2]) (by omega_using [e2, l2]) l3 e3,
    show regsVal s3 (low 4) + (if b.toNat = 1 then p else 0) = regsVal s4 (low 4) + 2 ^ 256 * s4.c.toNat by
      rw [e4]; cases b <;> rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l4]

/-! ### Half -/

private theorem halfMask_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block halfMask) s fun t =>
      t.gpr .x17 = (if decide (regsVal s (low 4) % 2 = 1) then -1 else 0) ∧ Keeps [.x17] s t := by
  apply WP.of_runBlock
  simp only [halfMask, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 63 < 64 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have e : regsVal s (low 4) % 2 = (s.gpr .x8).toNat % 2 := by
      rw [words]; unfold four; omega_using []
    rw [e]
    have h := (s.gpr .x8).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    simp only [decide_eq_true_eq]
    split <;> rename_i hb
    · rw [show (-1 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
      omega_using [hb, h]
    · rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega_using [hb, h]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

private theorem halfShift_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block halfShift) s fun t =>
      regsVal t (low 4) = (regsVal s (low 4) + 2 ^ 256 * s.c.toNat) / 2 ∧ Keeps [.x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [halfShift, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits, show 1 < 64 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [words, words]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    unfold four
    simp only [BitVec.setWidth_eq]
    rw [extr_toNat, extr_toNat, extr_toNat, extr_toNat]
    have hc : ((0 : BitVec 64) + 0 + BitVec.ofNat 64 s.c.toNat).toNat = s.c.toNat := by cases s.c <;> rfl
    rw [hc]
    have h0 := (s.gpr .x8).isLt
    have h1 := (s.gpr .x9).isLt
    have h2 := (s.gpr .x10).isLt
    have h3 := (s.gpr .x11).isLt
    have hb := Bool.toNat_le s.c
    omega_using [h0, h1, h2, h3, hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Half of a residue. -/
def halfP : Nat := (p + 1) / 2

private theorem half_arith {x : Nat} (hx : x < p) :
    (x + (if x % 2 = 1 then p else 0)) / 2 < p ∧
    2 * ((x + (if x % 2 = 1 then p else 0)) / 2) % p = x := by
  have hp : p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := rfl
  split <;> rename_i h
  · refine ⟨by omega_using [hx, hp], ?_⟩
    rw [show 2 * ((x + p) / 2) = x + p by omega_using [h, hp], Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · refine ⟨by omega_using [hx], ?_⟩
    rw [show 2 * ((x + 0) / 2) = x by omega_using [h], Nat.mod_eq_of_lt hx]

theorem half_ok {s : State} {base : Addr} {size o a : Nat} (hs : Scr s base size)
    (ho : o + 32 ≤ size) (ha : a + 32 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hA : wordsVal s.mem base a 4 < p) :
    WP isa (.block (half o a)) s fun t =>
      OpKeep Impl.P256.VerifySparse.M base o s t ∧ wordsVal t.mem base o 4 < p ∧
      2 * wordsVal t.mem base o 4 % p = wordsVal s.mem base a 4 := by
  obtain hf : Fresh (low 4) := by unfold Fresh; decide
  rw [half, show zero7 :: loads (low 4) a = [zero7] ++ loads (low 4) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s0 ⟨z0, k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) (hs.of_keeps k0 (by decide)) (a := a) ha ha8 hf) fun s1 ⟨e1, k1, _⟩ => ?_
  have z1 : s1.gpr .x7 = 0 := by rw [k1.gpr _ (by decide), z0]
  change regsVal s1 (low 4) = wordsVal s0.mem base a 4 at e1
  rw [k0.mem] at e1
  rw [WP.block_append_iff]
  refine WP.mono (halfMask_ok s1 z1) fun s2 ⟨m2, k2⟩ => ?_
  have z2 : s2.gpr .x7 = 0 := by rw [k2.gpr _ (by decide), z1]
  rw [WP.block_append_iff]
  refine WP.mono (addPrime_ok s2 _ z2 m2) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (halfShift_ok s3 (by rw [k3.gpr _ (by decide), z2])) fun s4 ⟨e4, k4⟩ => ?_
  have keep : Keeps (clob 4) s s4 := (((k0.mono (by decide)).trans (k1.mono (by decide))).trans
    (k2.mono (by decide))).trans ((k3.mono (by decide)).trans (k4.mono (by decide)))
  refine WP.mono (stores_ok (low 4) (hs.of_keeps keep (by decide)) (o := o) ho ho8 hf.1) fun t ⟨et, kt, ot⟩ => ?_
  refine ⟨⟨fun r hr => (kt.gpr r (by simp)).trans (keep.gpr r hr), kt.rd.trans keep.rd, kt.wr.trans keep.wr,
    kt.sp.trans keep.sp, fun x hx _ => (ot x hx).trans (congrFun keep.mem x)⟩, ?_⟩
  change wordsVal t.mem base o 4 = regsVal s4 (low 4) at et
  have er : regsVal s2 (low 4) = regsVal s1 (low 4) := regsVal_congr fun q hq =>
    k2.gpr q ((by decide : ∀ q ∈ low 4, q ∉ [Reg.x17]) q hq)
  rw [er, e1] at e3
  simp only [decide_eq_true_eq] at e3
  rw [et, e4, e3]
  exact half_arith hA

/-! ### The raw program -/

open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass
open EcdhJac (C K M Sl live layout aligned)
open VG.Impl.P256.VerifyArithmetic (operations)

/-- The inverse of two. -/
def halfE : Fe C := Fin.ofNat C.p halfP

private theorem halfE_two : (2 : Fe C) * halfE = 1 := by decide +kernel

/-- The slot a step writes, those it reads, and its effect on field values (`h` for one half). -/
def out : Step → Nat
  | .field f => f.out
  | .triple o _ | .half o _ => o
def ins : Step → List Nat
  | .field f => f.ins
  | .triple _ a | .half _ a => [a]
def run {F : Type _} [Lean.Grind.CommRing F] (h : F) (E : Nat → F) : Step → Nat → F
  | .field f => f.run E
  | .triple o a => Function.update E o (3 * E a)
  | .half o a => Function.update E o (h * E a)
def runs {F : Type _} [Lean.Grind.CommRing F] (h : F) (l : List Step) (E : Nat → F) : Nat → F := l.foldl (run h) E

/-- The slots that hold field values after the steps, when each reads only such slots. -/
def defined : List Step → List Nat → Option (List Nat)
  | [], V => some V
  | st :: l, V => if (ins st).all (· ∈ V) then defined l (out st :: V) else none

private theorem step_ok {M : Mod} (hME : M = Impl.P256.VerifySparse.M) {Sl : Nat → Prop} (hL : Lay M 8192 Sl)
    (hAl : Aligned M Sl) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State} (st : Step)
    (hS : ∀ x ∈ out st :: ins st, Sl x) (hR : ∀ x ∈ ins st, x ∈ V) (hi : Inv M base 8192 C.p Sl V E s) :
    WP isa (.block st.code) s fun t => Inv M base 8192 C.p Sl (out st :: V) (run halfE E st) t := by
  obtain hn : M.n = 4 := hME ▸ rfl
  have len (x : Nat) (hx : Sl x) : x + 32 ≤ 8192 := by
    have := hL.le x hx; rw [hn] at this; exact this
  cases st with
  | field f =>
    exact WP.mono (VerifySparse.fop_ok hME (m := C.p) rfl hL hAl (unitMod_pow_two (by decide) _) hi hS hR)
      fun _ h => h.2
  | triple o a =>
    have so := hS o (by simp [out]); have sa := hS a (by simp [ins]); have va := hR a (by simp [ins])
    have lt := hi.lt a va; rw [hn] at lt
    refine WP.mono (triple_ok hi.scr (len o so) (len a sa) (hAl.sl o so) (hAl.sl a sa) lt) fun t ⟨k, e⟩ => ?_
    refine hi.update hL so (hME ▸ k) (by rw [hn, e]; exact Nat.mod_lt _ (by decide)) ?_
    rw [← hi.val a va, hn, e]
    unfold toM
    rw [show (p : Nat) = C.p from rfl, ofNat_mod, ofNat_mul', Lean.Grind.Semiring.mul_assoc]; rfl
  | half o a =>
    have so := hS o (by simp [out]); have sa := hS a (by simp [ins]); have va := hR a (by simp [ins])
    have lt := hi.lt a va; rw [hn] at lt
    refine WP.mono (half_ok hi.scr (len o so) (len a sa) (hAl.sl o so) (hAl.sl a sa) lt) fun t ⟨k, b, e⟩ => ?_
    refine hi.update hL so (hME ▸ k) (by rw [hn]; exact b) ?_
    rw [← hi.val a va, hn, ← e]
    unfold toM
    rw [show (p : Nat) = C.p from rfl, ofNat_mod, ofNat_mul', ← Lean.Grind.Semiring.mul_assoc,
      ← Lean.Grind.Semiring.mul_assoc, Lean.Grind.CommSemiring.mul_comm halfE,
      show Fin.ofNat C.p 2 * halfE = 1 from halfE_two, Lean.Grind.Semiring.one_mul]

private theorem steps_ok {M : Mod} (hME : M = Impl.P256.VerifySparse.M) {Sl : Nat → Prop} (hL : Lay M 8192 Sl)
    (hAl : Aligned M Sl) {base : Addr} {U : List Nat} : ∀ (l : List Step) {V : List Nat} {E : Nat → Fe C} {s : State},
    (∀ st ∈ l, ∀ x ∈ out st :: ins st, Sl x) → defined l V = some U → Inv M base 8192 C.p Sl V E s →
    WP isa (.block (l.flatMap Step.code)) s fun t => Inv M base 8192 C.p Sl U (runs halfE l E) t
  | [], _, _, _, _, hd, hi => WP.block_nil (by cases hd; exact hi)
  | st :: l, V, _, _, hS, hd, hi => by
    by_cases h : (ins st).all (· ∈ V) = true
    · rw [defined, ite_eq_left h] at hd
      rw [List.flatMap_cons, WP.block_append_iff]
      exact WP.mono (step_ok hME hL hAl st (hS st (List.mem_cons_self ..))
        (by simpa only [List.all_eq_true, decide_eq_true_eq] using h) hi) fun _ i =>
          steps_ok hME hL hAl l (fun st' h' => hS st' (List.mem_cons_of_mem _ h')) hd i
    · rw [defined, ite_eq_right h] at hd; cases hd

/-- `defined` reads membership only, so it is the same for any list that has the point. -/
private theorem defined_append : ∀ (l : List Step) {V U : List Nat} (W : List Nat), defined l V = some U →
    defined l (V ++ W) = some (U ++ W)
  | [], _, _, _, h => by cases h; rfl
  | st :: l, V, U, W, h => by
    by_cases hc : (ins st).all (· ∈ V) = true
    · rw [defined, ite_eq_left hc] at h
      rw [defined, ite_eq_left (by
        simp only [List.all_eq_true, decide_eq_true_eq] at hc ⊢
        exact fun x hx => List.mem_append_left _ (hc x hx))]
      exact defined_append l W h
    · rw [defined, ite_eq_right hc] at h; cases h

private theorem point_run {F : Type _} [Lean.Grind.CommRing F] {h : F} (h2 : 2 * h = 1) (E : Nat → F) :
    (runs h steps E 512, runs h steps E 544, runs h steps E 576) = dblJF (E 512) (E 544) (E 576) := by
  simp only [runs, steps, run, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
    Nat.reduceEqDiff, ite_true, ite_false, dblJF, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

private theorem runs_other {h : Fe C} {x : Nat} : ∀ (l : List Step) (E : Nat → Fe C), (∀ st ∈ l, out st ≠ x) →
    runs h l E x = E x
  | [], _, _ => rfl
  | st :: l, E, hx => by
    have n : x ≠ out st := fun e => hx st (List.mem_cons_self ..) e.symm
    refine (runs_other l (run h E st) fun st' h' => hx st' (List.mem_cons_of_mem _ h')).trans ?_
    cases st with
    | field f =>
      refine runOps_of_not_out [f] E ?_
      intro f' hf e
      rw [List.mem_singleton.mp hf] at e
      exact n e.symm
    | triple o a => exact Function.update_of_ne n _ _
    | half o a => exact Function.update_of_ne n _ _

/-- The slots the steps use. -/
def slotsUsed : List Nat := [512, 544, 576, 800, 832, 864, 896, 928]

/-- On the callers' live slots the steps have the effect of the field program their statements name. -/
private theorem runs_eq (E : Nat → Fe C) {x : Nat}
    (h : x ∈ [512, 544, 576] ∨ x ∉ slotsUsed ∧ ∀ op ∈ operations .doubleRR, op.out ≠ x) :
    runs halfE steps E x = runOps (operations .doubleRR) E x := by
  rcases h with hm | ⟨hn, ho⟩
  · have e := (point_run halfE_two E).trans (dblJMul_inplace_run (S := Impl.P256.VerifyDouble.S)
      (p := Impl.P256.VerifyDouble.R) (by decide +kernel) E).symm
    simp only [Prod.mk.injEq] at e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact e.1
    · exact e.2.1
    · exact e.2.2
  · rw [runOps_of_not_out _ _ ho]
    exact runs_other steps E fun st hs e => hn (e ▸ (by decide : ∀ st ∈ steps, out st ∈ slotsUsed) st hs)

/-- The allocated doubling, for any live slots but its temporaries. -/
theorem program_ok {M : Mod} (hME : M = Impl.P256.VerifySparse.M) {Sl : Nat → Prop} (hL : Lay M 8192 Sl)
    (hAl : Aligned M Sl) (hS : ∀ x ∈ slotsUsed, Sl x) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hV : ∀ x ∈ [512, 544, 576], x ∈ V)
    (hR : ∀ x ∈ V, x ∈ [512, 544, 576] ∨ x ∉ slotsUsed ∧ ∀ op ∈ operations .doubleRR, op.out ≠ x)
    (hO : ∀ x ∈ V, ∀ i < 4, VerifyAllocated.observe .doubleRR (x + 8 * i))
    (hi : Inv M base 8192 C.p Sl V E s) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base VerifyAllocated.work s t ∧
      Inv M base 8192 C.p Sl V (runOps (operations .doubleRR) E) t := by
  obtain hn : M.n = 4 := hME ▸ rfl
  obtain ⟨U, hU⟩ : ∃ U, defined steps [512, 544, 576] = some U := ⟨_, rfl⟩
  have point : Inv M base 8192 C.p Sl ([512, 544, 576] ++ V) E s := hi.sub fun x hx =>
    (List.mem_append.mp hx).elim (hV x) id
  have raw : WP isa (.block Impl.P256.EcdhDouble.raw) s fun t =>
      Inv M base 8192 C.p Sl V (runOps (operations .doubleRR) E) t :=
    WP.mono (steps_ok hME hL hAl steps (fun st hs x hx => hS x
      ((by decide : ∀ st ∈ steps, ∀ x ∈ out st :: ins st, x ∈ slotsUsed) st hs x hx)) (defined_append steps V hU) point)
      fun t it => (it.sub fun x hx => List.mem_append_right _ hx).congr_env fun x hx => runs_eq E (hR x hx)
  refine WP.mono (Certificate.refine hi.scr raw) fun t ⟨u, hu, ho, hk⟩ => ⟨hk, ?_⟩
  have hs := hk.scr allocatedRegs_x0 hi.scr
  have hm := hi.mod.unch hk.unch
    (show ∀ w ∈ VerifyAllocated.work, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo by subst hME; decide) hi.scr.nowrap
  apply hu.of_observed hs hm
  intro x hx i him
  rw [hn] at him
  have ha := hAl.sl x (hi.sl x hx)
  have hb := hL.le x (hi.sl x hx)
  rw [hn] at hb
  exact ho (x + 8 * i) (hO x hx i him) (by omega_using [ha]) (by omega_using [hb, him])

/-- The doubling of ECDH's window. -/
theorem double_ok (hC : Law C) (ha : AM3 C) {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C} (hp : onCurve C P = true)
    (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base EcdhJac.work s t ∧
      Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) :=
  WP.mono (program_ok rfl layout aligned (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hi) fun _ ⟨hk, it⟩ =>
    ⟨hk.mono (fun _ h => h) (by decide), it,
      InvJ.dbl' hC ha hp hj (dblJMul_inplace_run (by decide +kernel) E)⟩

end VG.Proof.P256.EcdhDouble
