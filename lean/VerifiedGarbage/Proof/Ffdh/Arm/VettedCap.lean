module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapSelect
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapStore
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! # Verified installation of a public vetted exponent cap -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.VettedCap
open VG.Proof.X25519.Arm (Rest)

theorem code_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (common : sampleSlots slots) :
    WP isa code s fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 =
        (result choices (s.gpr .r11) (s.mem.readW (off (State.addr s.sp) 20) 32,
          s.mem.readW (off (State.addr s.sp) 68) 32)).1 ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 =
        (result choices (s.gpr .r11) (s.mem.readW (off (State.addr s.sp) 20) 32,
          s.mem.readW (off (State.addr s.sp) 68) 32)).2 ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (load_ok s h) ?_
  rintro u ⟨⟨width, mask, memU⟩, restU⟩
  have contextU := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  rw [WP.seq_iff]
  refine WP.mono (choose_ok choices u) ?_
  rintro v ⟨value, memV, restV⟩
  have contextV := contextU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
  refine WP.mono (save_ok v contextV common) ?_
  rintro t ⟨context, countT, maskT, frameT, restT⟩
  rw [restU.gpr .r11 (by simp), width, mask] at value
  have first := congrArg Prod.fst value
  have second := congrArg Prod.snd value
  have frame : Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem := by
    rw [memV, memU, restV.sp, restU.sp] at frameT
    exact frameT
  exact ⟨context, countT.trans first, maskT.trans second, frame,
    ((restU.mono (by simp [roundClobbers])).trans (restV.mono (by simp [roundClobbers]))).trans
      (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Ffdh.Arm.VettedCap
