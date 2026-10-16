module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptInput
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The CRT ciphertext range check and saved acceptance remain secret -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_acceptInput_ct {base src : BitVec 32} {len w k : Nat} {bs1 bs2 : List Byte} :
    RelCT isa (fun s t => CrtAcceptInput base src len w k bs1 s ∧
      CrtAcceptInput base src len w k bs2 t ∧ s.sp = t.sp) CrtFn.acceptInput (fun _ _ => True) := by
  let P := fun s t => CrtAcceptInput base src len w k bs1 s ∧
    CrtAcceptInput base src len w k bs2 t ∧ s.sp = t.sp
  have load : RelCT isa P (savedOperand 1 56 12) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.source⟩, ⟨h.2.1.ready, h.2.1.source⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) {bs : List Byte} (h : CrtAcceptInput base src len w k bs s) :
      WP isa (savedOperand 1 56 12) s (LayoutFrameReady base len w) :=
    WP.mono (savedOperandLayout_ok s h.ready h.source (by decide : 1 < 8) h.positive h.fits) (fun _ j => j.1)
  have first := (relCT_keep_sp load (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have compare : RelCT isa (fun s t => s.sp = t.sp ∧ LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t)
      inputCompare (fun _ _ => True) :=
    inputCompareLayout_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  exact first.seq ((relCT_keep_sp compare (fun _ _ h => h.1)).seq saveAcceptance_ct)

end VG.Proof.Bignum.Arm
