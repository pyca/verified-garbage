module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundArgs
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundSave
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScan
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySmear
import VerifiedGarbage.Proof.Framework.Block

/-! Derive the exact native scalar width and mask from the public domain bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyBound_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound s fun t =>
      (Context p (68 :: 20 :: slots) t ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem) ∧
      Rest [.r3, .r4, .r6, .r11, .r12] s t := by
  refine withRest [.r3, .r4, .r6, .r11, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try decide +kernel
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound, WP.seq_iff]
  refine WP.mono (keyBoundArgs_ok s h h24 h28 h32 h60) ?_
  rintro u ⟨⟨ptr, count, memU⟩, restU⟩
  have ctxU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  rw [WP.seq_iff]
  refine WP.mono (keyScan_ok u ctxU.boundBytes (by rw [p.boundOctetsLength]; have := p.minLength; omega)
    (by rw [p.boundOctetsLength]; have := p.maxLength; omega) ptr (by rw [p.boundOctetsLength]; exact count)) ?_
  rintro v ⟨_, countV, byteV, memV, restV⟩
  have ctxV := ctxU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans ctxU.ptr)
  rw [WP.block_append_iff]
  refine WP.mono (smear_ok v byteV) ?_
  rintro w ⟨⟨mask, memW⟩, restW⟩
  have ctxW := ctxV.of_mem memW restW ((restW.gpr .r0 (by simp)).trans ctxV.ptr)
  have countW : w.gpr .r6 = BitVec.ofNat 32 p.scalarWidth := by
    rw [restW.gpr .r6 (by simp), countV, p.boundOctetsLength]
    rfl
  have maskW : w.gpr .r3 = p.scalarMask := by
    rw [mask, smear32_eq]
    rfl
  refine WP.mono (keyBoundSave_ok w ctxW stable countW maskW) ?_
  rintro t ⟨ctxT, frame, _⟩
  rw [memW, memV, memU, restW.sp, restV.sp, restU.sp] at frame
  exact ⟨ctxT, frame⟩

end VG.Proof.Ffdh.Arm
