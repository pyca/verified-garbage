module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainPointers
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
/-! Public modulus validation precedes every native FFDH operation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem headPrefix_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers)) s fun t =>
      Context p (60 :: 56 :: slots) t ∧ t.gpr .r4 = p.domain ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.block_append_iff]
  refine WP.mono (prepareArgs_ok s 24 h stable h24 h32 h0) ?_
  rintro u ⟨contextU, _, srcU, countU, stackU, frameU, restU⟩
  refine WP.mono (domainPointers_ok u contextU stable srcU countU (stackU.trans restU.sp.symm)) ?_
  rintro t ⟨contextT, frameT, restT⟩
  have fU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := frameU.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp, ?_⟩
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  rw [restU.sp] at frameT
  have fT : Frame [⟨State.addr s.sp, 72⟩] u.mem t.mem := frameT.sub (by
    intro r hr
    refine ⟨⟨State.addr s.sp, 72⟩, by simp, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  exact ⟨contextT, (restT.gpr .r4 (by simp)).trans srcU, (restT.gpr .r6 (by simp)).trans countU,
    fU.trans fT, (restU.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩

theorem head_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
      (.block VG.Impl.Bignum.Arm.modulusCheck)) s fun t =>
      Context p (60 :: 56 :: slots) t ∧ t.z = Spec.Rsa.modulusValid p.P p.k ∧
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (headPrefix_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, srcU, countU, frameU, restU⟩
  have pBytes := contextU.pBytes
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
    simpa only [p.pLength] using pBytes.bytes
  refine WP.mono (modulusCheck_ok u p.minLength p.maxLength
    (by rw [← p.pLength]; exact pBytes.fits) (by rw [← p.pLength]; exact pBytes.readable) srcU countU) ?_
  rintro t ⟨zero, memT, restT⟩
  rw [bytes] at zero
  have frameT : Frame [⟨State.addr p.base, 8 * p.len⟩] u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  refine ⟨contextU.after_workspace frameT restT ((restT.gpr .r0 (by simp)).trans contextU.ptr)
    (fun d hd => (stableSlots_at stable' hd).1), zero, ?_, ?_⟩
  · rw [memT]; exact frameU
  · exact restU.trans (restT.mono (by simp [roundClobbers]))

end VG.Proof.Ffdh.Arm
