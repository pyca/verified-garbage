module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Prepare the compact Miller–Rabin constants through RSA's existing
array routines. Clearing native padding makes both views agree exactly. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num Keep opRegs)
open VG.Proof.Rsa.Mont (numAt)

private theorem subtract_exact {a b r modulus borrow : Nat} (le : b ≤ a) (small : r < modulus)
    (value : r + b = a + modulus * borrow) (bit : borrow ≤ 1) : r = a - b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bit with zero | one
  · rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  · rw [one, Nat.mul_one] at value
    omega

theorem montKeyArrays_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem)
    (rSmall : numAt s.mem (State.addr base) w 1 ≤ numAt s.mem (State.addr base) w 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      Keep (base + 96#32) (2 * w + 2) [0, 1, 9, 10] [] s.mem t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 0 = numAt s.mem (State.addr base) w 0 ∧
      num t.mem (base + 96#32) (2 * w + 2) 9 = numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 9 = numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 10 =
        numAt s.mem (State.addr base) w 0 - numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Rest opRegs s t := by
  have fits := ready.baseShiftFits workspace
  have nBound := numAt_lt s.mem (State.addr base) w 0
  have rBound : numAt s.mem (State.addr base) w 1 < 2 ^ (64 * w) := Nat.lt_of_le_of_lt rSmall nBound
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs ]
  refine WP.seq (WP.mono (keyClrTop_ok workspace ready (j := 0) (by decide)) ?_)
  rintro s1 ⟨ready1, keep1, n1, rest1⟩
  have workspace1 := workspace.congr rest1.wr
  have r1 := key_keep_number workspace ready (j := 1) (by decide) (by simp) keep1
  refine WP.seq (WP.mono (keyClrTop_ok workspace1 ready1 (j := 1) (by decide)) ?_)
  rintro s2 ⟨ready2, keep2, r2, rest2⟩
  rw [r1] at r2
  have workspace2 := workspace1.congr rest2.wr
  have n2 := (keep2.num (j := 0) (by simp) (by simp) (ready1.fit64 (by decide))).trans n1
  refine WP.seq (WP.mono (keyCopy_ok workspace2 ready2 (o := 9) (a := 1) (by decide) (by decide) (by decide)) ?_)
  rintro s3 ⟨ready3, keep3, r3, rest3⟩
  rw [r2] at r3
  have workspace3 := workspace2.congr rest3.wr
  have n3 := (keep3.num (j := 0) (by simp) (by simp) (ready2.fit64 (by decide))).trans n2
  refine WP.seq (WP.mono (keySub3_ok workspace3 ready3 (o := 10) (a := 0) (b := 9)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_)
  rintro t ⟨ready4, keep4, difference, borrow, rest4⟩
  rw [n3, r3] at difference
  have exactDifference := subtract_exact rSmall
    (val32_lt t.mem (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) 10) (2 * w + 2))
    difference borrow
  change num t.mem (base + 96#32) (2 * w + 2) 10 = _ at exactDifference
  have n4 := (keep4.num (j := 0) (by simp) (by simp) (ready3.fit64 (by decide))).trans n3
  have r4 := (keep4.num (j := 9) (by simp) (by simp) (ready3.fit64 (by decide))).trans r3
  have number0 : numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
    rw [keyView_number_low t.mem base w 0 fits (by rw [n4]; exact nBound), n4]
  have number9 : numAt t.mem (State.addr base) w 9 = numAt s.mem (State.addr base) w 1 := by
    rw [keyView_number_low t.mem base w 9 fits (by rw [r4]; exact rBound), r4]
  have number10 : numAt t.mem (State.addr base) w 10 =
      numAt s.mem (State.addr base) w 0 - numAt s.mem (State.addr base) w 1 := by
    rw [keyView_number_low t.mem base w 10 fits (by rw [exactDifference]; omega), exactDifference]
  have keep : Keep (base + 96#32) (2 * w + 2) [0, 1, 9, 10] [] s.mem t.mem :=
    ((keep1.mono (by simp)).trans (keep2.mono (by simp))).trans
      ((keep3.mono (by simp)).trans (keep4.mono (by simp)))
  have frame := key_keep_frame workspace ready (by simp) keep
  have data4 := data.after_value frame (keyArrayRegions.header workspace ready (by simp)) number0
  exact WP.block_nil ⟨ready4, data4.1, keep, n4, r4, number9, number10, number0,
    rest1.trans (rest2.trans (rest3.trans rest4))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
