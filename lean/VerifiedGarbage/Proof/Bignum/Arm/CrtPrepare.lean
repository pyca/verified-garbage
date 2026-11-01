module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
import VerifiedGarbage.Proof.Bignum.Arm.CrtSaveMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete CRT preparation imports n and preserves all three workspace layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_prepare_ok (s : State) {base np : BitVec 32} {size w k : Nat} {nb : List Byte}
    (h : CrtPrepareInput base np size w k nb s) :
    WP isa CrtFn.prepare s fun t => CrtLoaded base size w t ∧
      t.mem.readW (off (State.addr t.sp) 8) 32 = base ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip nb ∧
      Frame [⟨State.addr base, size⟩, ⟨off (State.addr s.sp) 8, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_initialize_ok s h) ?_
  rintro u ⟨initialized, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_importModulus_ok u initialized) ?_
  rintro v ⟨loaded, value, frameV, restV⟩
  have frameV' : Frame [⟨State.addr base, size⟩] u.mem v.mem := frameV.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_, List.mem_singleton_self _, crt_region_sub_workspace h.workspace h.storageFits (by simp [crtRegions])⟩)
  refine WP.mono (crt_saveMain_ready v loaded) ?_
  rintro t ⟨ready, saved, valueT, frameT, restT⟩
  have rest := restU.trans restV
  rw [rest.sp] at frameT
  exact ⟨ready, saved, valueT.trans value,
    ((frameU.trans frameV').mono (by simp)).trans (frameT.mono (by simp)),
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
