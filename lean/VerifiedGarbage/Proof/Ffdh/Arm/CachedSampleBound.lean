module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleHead
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapStore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.TCB.Code
/-! Canonical public metadata installs the reviewed scalar width and mask. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedMask.lean`, which only this module imported.
section

/-! Three public conditional immediate shifts implement the cached scalar mask. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedSampleMask.lean`, which only this module imported.
section

/-! The cached sampler's three public mask shifts form one shared computation. -/

section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem mask_ok (s : State) {count : Nat} (fit : count < 8)
    (source : s.gpr .r9 = BitVec.ofNat 32 count) (initial : s.gpr .r3 = 255) :
    WP isa VG.Impl.Ffdh.Arm.CachedSample.mask s fun t =>
      t.gpr .r3 = (BitVec.ofNat 32 255) >>> count ∧ t.mem = s.mem ∧ Rest [.r3, .r12] s t := by
  rw [VG.Impl.Ffdh.Arm.CachedSample.mask, WP.seq_iff]
  refine WP.mono (maskShift_ok s 4 4 (by decide) (by decide) (by decide)) ?_
  rintro u ⟨valueU, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskShift_ok u 2 2 (by decide) (by decide) (by decide)) ?_
  rintro v ⟨valueV, memV, restV⟩
  refine WP.mono (maskShift_ok v 1 1 (by decide) (by decide) (by decide)) ?_
  rintro t ⟨valueT, memT, restT⟩
  have countU := (restU.gpr .r9 (by simp)).trans source
  have countV := (restV.gpr .r9 (by simp)).trans countU
  rw [countV, valueV, countU, valueU, source, initial, maskShifts_value count fit] at valueT
  exact ⟨valueT, memT.trans (memV.trans memU), (restU.trans restV).trans restT⟩

end VG.Proof.Ffdh.Arm.CachedSample
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem layout_width (p : Inputs) (positive : 0 < bits p) :
    (ScalarLayout.vetted p).width = (bits p + 7) / 8 := by
  have fit := VG.Proof.Ffdh.ScalarWidth.width_le (by have := p.minLength; omega : 0 < p.k)
    (Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.bits_le_bound _) p.scalarBound_bits_fit)
  change p.k - (p.k - VG.Proof.Ffdh.ScalarWidth.width (bits p)) = _
  change VG.Proof.Ffdh.ScalarWidth.width (bits p) ≤ p.k at fit
  rw [Nat.sub_sub_self fit]
  unfold VG.Proof.Ffdh.ScalarWidth.width
  omega

theorem bound_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (environment : CachedGenerationContext p s)
    (h52 : 52 ∈ slots) (special : sampleSlots slots)
    (positive : 0 < bits p) (bound : bits p ≤ 8192) :
    WP isa VG.Impl.Ffdh.Arm.CachedSample.bound s fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 (ScalarLayout.vetted p).width ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = (ScalarLayout.vetted p).mask ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CachedSample.bound, WP.seq_iff]
  refine WP.mono (head_ok s h environment h52) ?_
  rintro u ⟨⟨widthU, countU, maskU, memU⟩, restU⟩
  have countEq := VG.Proof.Ffdh.ScalarWidth.mask_shift_count positive bound
  change shiftCount (bits p) = BitVec.ofNat 32 (7 - (bits p - 1) % 8) at countEq
  rw [countEq] at countU
  rw [WP.seq_iff]
  refine WP.mono (mask_ok u (by omega : 7 - (bits p - 1) % 8 < 8) countU maskU) ?_
  rintro v ⟨maskV, memV, restV⟩
  rw [VG.Proof.Ffdh.ScalarWidth.mask_shift32 positive] at maskV
  have ptrV := (restV.gpr .r0 (by simp)).trans ((restU.gpr .r0 (by simp)).trans h.ptr)
  have contextV := (h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)).of_mem memV restV ptrV
  refine WP.mono (VettedCap.save_ok v contextV special) ?_
  rintro t ⟨contextT, widthT, maskT, frameT, restT⟩
  have widthV := (restV.gpr .r6 (by simp)).trans widthU
  rw [widthV, ← layout_width p positive] at widthT
  have maskValue : v.gpr .r3 = (ScalarLayout.vetted p).mask := maskV
  rw [maskValue] at maskT
  rw [memV, memU, restV.sp, restU.sp] at frameT
  exact ⟨contextT, widthT, maskT, frameT,
    (restU.mono (by simp [roundClobbers])).trans
      ((restV.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers])))⟩

end VG.Proof.Ffdh.Arm.CachedSample
