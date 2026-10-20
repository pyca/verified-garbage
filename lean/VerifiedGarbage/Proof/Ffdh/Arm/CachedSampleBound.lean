module

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleHead
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleMask
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapStore
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth

/-! Canonical public metadata installs the reviewed scalar width and mask. -/

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
