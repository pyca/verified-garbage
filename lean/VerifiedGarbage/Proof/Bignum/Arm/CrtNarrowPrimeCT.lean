module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Preparing the factor in the narrow workspace hides the factor and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_narrowPrime_ct {base pp : BitVec 32} {len v k ps : Nat} {pb1 pb2 : List Byte}
    (countFits : 128 * v < 2 ^ 32) :
    RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧ NarrowPrimeInput base pp len v k ps pb2 t ∧
      s.sp = t.sp) (narrowPrime ps) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧
      NarrowPrimeInput base pp len v k ps pb2 t ∧ s.sp = t.sp) (savedOperand 0 ps (ps + 4)) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.toLayoutFrameReady, h.1.source⟩, ⟨h.2.1.toLayoutFrameReady, h.2.1.source⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have wp (s : State) {pb : List Byte} (h : NarrowPrimeInput base pp len v k ps pb s) :
      WP isa (savedOperand 0 ps (ps + 4)) s (AcceptedPrimeInput base len v) :=
    (crt_narrowImport_ok s h).mono fun _ j => j.1
  rw [narrowPrime]
  exact crt_seq_ct load (fun s h => wp s h) (fun s h => wp s h) (prepareAcceptedPrime_ct countFits)

end VG.Proof.Bignum.Arm
