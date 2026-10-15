module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCallsCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivTailCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The full private body has the same trace for independent secret inputs -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

theorem privateCheck_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivateState g bs1 s ∧ PrivateState g bs2 t ∧ s.sp = t.sp)
      (check v.pcName v.pc v.pdName v.pd) (fun _ _ => True) := by
  unfold check
  apply crt_seq_ct (pcArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s h => pcArgs_ready s h) (fun s h => pcArgs_ready s h)
  apply crt_seq_ct (pcCall_ct v nb) (fun s h => pcCall_ready v s h) (fun s h => pcCall_ready v s h)
  apply crt_seq_ct (pdArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s h => pdArgs_ready s h) (fun s h => pdArgs_ready s h)
  apply crt_seq_ct (pdCall_ct v nb eb) (fun s h => pdCall_ready v s h) (fun s h => pdCall_ready v s h)
  exact tail_ct.mono (fun _ _ h => ⟨h.1.context.tailInput h.1.slots,
    h.2.1.context.tailInput h.2.1.slots, h.2.2⟩) (fun _ _ _ => trivial)

theorem privateBody_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivateStart g bs1 s ∧ PrivateStart g bs2 t ∧ s.sp = t.sp)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (fun _ _ => True) := by
  unfold body
  apply crt_seq_ct (crtArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s h => crtArgs_ready s h) (fun s h => crtArgs_ready s h)
  exact crt_seq_ct (crtCall_ct v nb) (fun s h => crtCall_ready v s h) (fun s h => crtCall_ready v s h) (privateCheck_ct v nb eb)
end VG.Proof.Rsa.Arm
