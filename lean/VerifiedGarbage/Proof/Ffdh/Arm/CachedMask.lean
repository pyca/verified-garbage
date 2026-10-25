module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X25519.Arm.Instr

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Code

/-! Three public conditional immediate shifts implement the cached scalar mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def maskShiftResult (bit amount : Nat) (count mask : BitVec 32) : BitVec 32 :=
  if count &&& BitVec.ofNat 32 bit == 0 then mask else mask >>> amount

theorem maskTest_ok (s : State) (bit : Nat) (encoded : encodable (BitVec.ofNat 32 bit) = true) :
    WP isa (.block [.dp .and .r12 .r9 (.imm (BitVec.ofNat 32 bit)), .cmp .r12 (.imm 0)]) s fun t =>
      (t.z = (s.gpr .r9 &&& BitVec.ofNat 32 bit == 0) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  ffrun [encoded]
  exact congrArg (fun x : BitVec 32 => x == 0) (BitVec.sub_zero (s.gpr .r9 &&& BitVec.ofNat 32 bit))

theorem maskMove_ok (s : State) (amount : Nat) (positive : 0 < amount) (fit : amount < 32) :
    WP isa (.block [.mov .r3 (.shifted .r3 .lsr amount)]) s fun t =>
      (t.gpr .r3 = s.gpr .r3 >>> amount ∧ t.mem = s.mem) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  ffrun [(by omega : 1 ≤ amount ∧ amount ≤ 31)]

theorem maskShift_ok (s : State) (bit amount : Nat) (encoded : encodable (BitVec.ofNat 32 bit) = true)
    (positive : 0 < amount) (fit : amount < 32) :
    WP isa (VG.Impl.Ffdh.Arm.CachedSample.maskShift bit amount) s fun t =>
      t.gpr .r3 = maskShiftResult bit amount (s.gpr .r9) (s.gpr .r3) ∧
      t.mem = s.mem ∧ Rest [.r3, .r12] s t := by
  rw [VG.Impl.Ffdh.Arm.CachedSample.maskShift, WP.seq_iff]
  refine WP.mono (maskTest_ok s bit encoded) ?_
  rintro u ⟨⟨flag, memU⟩, restU⟩
  have kept9 := restU.gpr .r9 (by simp)
  have kept10 := restU.gpr .r3 (by simp)
  cases eqn : (s.gpr .r9 &&& BitVec.ofNat 32 bit == 0) with
  | true =>
    refine WP.ite false (by change some (!u.z) = some false; rw [flag, eqn]; rfl) (by simp) ?_
    intro _
    apply WP.block_nil
    exact ⟨by simp only [maskShiftResult, eqn, ite_true]; exact kept10, memU, restU.mono (by simp)⟩
  | false =>
    refine WP.ite true (by change some (!u.z) = some true; rw [flag, eqn]; rfl) ?_ (by simp)
    intro _
    refine WP.mono (maskMove_ok u amount positive fit) ?_
    rintro t ⟨⟨value, memT⟩, restT⟩
    exact ⟨by simp only [maskShiftResult, eqn, Bool.false_eq_true, ite_false, value, kept10],
      memT.trans memU, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

theorem maskShifts_value (count : Nat) (fit : count < 8) :
    maskShiftResult 1 1 (BitVec.ofNat 32 count)
      (maskShiftResult 2 2 (BitVec.ofNat 32 count)
        (maskShiftResult 4 4 (BitVec.ofNat 32 count) 255)) =
      (BitVec.ofNat 32 255) >>> count := by
  have choices : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨
      count = 4 ∨ count = 5 ∨ count = 6 ∨ count = 7 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.Arm.CachedSample
