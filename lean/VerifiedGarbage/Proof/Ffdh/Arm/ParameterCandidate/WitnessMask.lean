module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskBits
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskStore
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words32
/-! Exact native witness truncation, using RSA's fixed-step word-mask
construction and the existing packed Montgomery operand. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/ParameterCandidate/WordCut32.lean`, which only this module imported.
section

/-! Cutting one occupied native word masks the complete packed integer,
including a partially occupied top word below the allocated width. -/

section
namespace VG.Proof.Ffdh.ParameterCandidate
open VG VG.Proof.Mont
open VG.Proof.Weierstrass (testBit_val32)

theorem testBit_mask32 {k : Nat} (bound : k ≤ 32) (i : Nat) :
    (BitVec.ofNat 32 (2 ^ k - 1)).toNat.testBit i = decide (i < k) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) bound
    have := Nat.two_pow_pos k
    omega), Nat.testBit_two_pow_sub_one]

theorem val32_cut {m m' : Mem} {base : Addr} {d w j k : Nat}
    (bits : k ≤ 32)
    (small : val32 m base d w < 2 ^ (32 * (j + 1)))
    (top : m'.readW (off base (d + 4 * j)) 32 =
      m.readW (off base (d + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (other : ∀ i, i < w → i ≠ j →
      m'.readW (off base (d + 4 * i)) 32 = m.readW (off base (d + 4 * i)) 32) :
    val32 m' base d w = val32 m base d w % 2 ^ (32 * j + k) := by
  have topNat := congrArg BitVec.toNat top
  rw [BitVec.toNat_and] at topNat
  change w32 m' base (d + 4 * j) = w32 m base (d + 4 * j) &&& _ at topNat
  have otherNat (i : Nat) (bound : i < w) (different : i ≠ j) :
      w32 m' base (d + 4 * i) = w32 m base (d + 4 * i) :=
    congrArg BitVec.toNat (other i bound different)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases within : i < 32 * w
  · have index : i / 32 < w := by omega
    have bit : i % 32 < 32 := Nat.mod_lt _ (by decide)
    have split : i = 32 * (i / 32) + i % 32 := by omega
    have readNew := testBit_val32 m' base d w (i / 32) (i % 32) index bit
    have readOld := testBit_val32 m base d w (i / 32) (i % 32) index bit
    rw [← split] at readNew readOld
    rw [readNew]
    by_cases atTop : i / 32 = j
    · rw [atTop, topNat, Nat.testBit_and, testBit_mask32 bits]
      rw [readOld, atTop]
      have same : decide (i % 32 < k) = decide (i < 32 * j + k) := decide_eq_decide.mpr (by omega)
      rw [same, Bool.and_comm]
    · rw [otherNat (i / 32) index atTop, ← readOld]
      by_cases below : i / 32 < j
      · have keep : i < 32 * j + k := by omega
        simp only [keep, decide_true, Bool.true_and]
      · have high : 32 * (j + 1) ≤ i := by omega
        have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) high))
        rw [zero]
        simp only [Bool.and_false]
  · have scale := Nat.pow_le_pow_right (by decide : 0 < 2) (show 32 * w ≤ i by omega)
    have oldZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m base d w) scale)
    have newZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' base d w) scale)
    rw [oldZero, newZero]
    simp only [Bool.and_false]

end VG.Proof.Ffdh.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)

theorem witnessMask_ok {s : State} {base : BitVec 32} {capacity w bits : Nat}
    (ready : ArithmeticReady base capacity w s) (stack : Workspace s s.sp 72)
    (positive : 0 < bits) (bound : bits ≤ 8192) (fitsBits : bits ≤ 64 * w)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits)
    (small : numAt s.mem (State.addr base) w 1 < 2 ^ (32 * ((bits - 1) / 32 + 1))) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask s fun t =>
      ArithmeticReady base capacity w t ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits ∧
      Keeps (State.addr base) capacity w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let j := (bits - 1) / 32
  let k := (bits - 1) % 32 + 1
  have geometry := witness_geometry positive fitsBits
  have jBound : j < 2 * w := geometry.1
  have kBound : k ≤ 32 := geometry.2.1
  have bitWidth : 32 * j + k = bits := geometry.2.2.1
  have fit : arrAt w 1 + 8 * (w + 2) ≤ 8 * capacity :=
    Nat.le_trans (array_end_le (w := w) (j := 1) (k := 8) (by decide)) (ready.width ▸ ready.layout.2.2.1)
  have nowrap := ready.workspace.nowrap
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (witnessMaskHead_ok stack positive bound saved) ?_)
  rintro u ⟨⟨indexU, countU, memU⟩, restU⟩
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  refine WP.seq (WP.mono (witnessMaskBits_ok kBound countU) ?_)
  rintro v ⟨maskV, memV, restV⟩
  have readyV := readyU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans readyU.ptr)
  have indexV : v.gpr .r5 = BitVec.ofNat 32 j := (restV.gpr .r5 (by simp)).trans indexU
  refine WP.seq (WP.mono (witnessMaskStore_ok readyV jBound indexV) ?_)
  rintro t ⟨⟨memT, ptrT⟩, restT⟩
  rw [maskV, memV, memU] at memT
  have outside := writeW32_outside s.mem (State.addr base)
    (s.mem.readW (off (State.addr base) (arrAt w 1 + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (d := arrAt w 1 + 4 * j) (by omega)
  rw [← memT] at outside
  have wide := outside.mono (o' := arrAt w 1) (n' := 8 * w) (by omega) (by omega)
  have keeps := outside_array_keeps wide (len := capacity) (by omega)
  have frame := outside_workspace wide (size := 8 * capacity) (by omega)
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    ((restV.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers])))
  have value : numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits := by
    rw [numAt_native, numAt_native, ← bitWidth]
    apply VG.Proof.Ffdh.ParameterCandidate.val32_cut kBound
    · rwa [← numAt_native]
    · rw [memT, Mem.readW_writeW_self32]
    · intro i bound different
      rw [memT, Mem.readW_writeW_sep (w := 32) (w' := 32)
        (Offset.sep _ (d := arrAt w 1 + 4 * i) (n := 4) (e := arrAt w 1 + 4 * j) (k := 4)
          (by omega) (by omega) (by omega)) (by decide)]
  exact WP.block_nil ⟨(ready.after_array (by decide) keeps frame rest ptrT).1, value, keeps, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
