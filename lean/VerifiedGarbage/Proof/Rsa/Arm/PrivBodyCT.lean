module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivStages

import VerifiedGarbage.Proof.Rsa.Arm.PrivCallsCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivTailContext
import VerifiedGarbage.Proof.Rsa.Arm.PrivTailCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

/-! # The full private body has the same trace for independent secret inputs -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

theorem privateCheckWith_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    {Q1 Q2 : State → Prop} (k1 : Kept g Q1) (k2 : Kept g Q2) {stage : Prog isa}
    (stageCt : RelCT isa (fun s t => (PcReady g bs1 s ∧ Q1 s) ∧ (PcReady g bs2 t ∧ Q2 t) ∧ s.sp = t.sp)
      stage (fun _ _ => True))
    (r1 : ∀ s, PcReady g bs1 s ∧ Q1 s → WP isa stage s (PcReturned g bs1))
    (r2 : ∀ s, PcReady g bs2 s ∧ Q2 s → WP isa stage s (PcReturned g bs2))
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivateState g bs1 s ∧ Q1 s) ∧ (PrivateState g bs2 t ∧ Q2 t) ∧ s.sp = t.sp)
      (checkWith stage v.pdName v.pd) (fun _ _ => True) := by
  unfold checkWith
  apply crt_seq_ct (pcArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (pcArgs_readyQ k1) (pcArgs_readyQ k2)
  apply crt_seq_ct stageCt r1 r2
  apply crt_seq_ct (pdArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s h => pdArgs_ready s h) (fun s h => pdArgs_ready s h)
  apply crt_seq_ct (pdCall_ct v nb eb) (fun s h => pdCall_ready v s h) (fun s h => pdCall_ready v s h)
  exact tail_ct.mono (fun _ _ h => ⟨h.1.context.tailInput h.1.slots,
    h.2.1.context.tailInput h.2.1.slots, h.2.2⟩) (fun _ _ _ => trivial)

theorem privateBodyWith_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    {Q1 Q2 : State → Prop} (k1 : Kept g Q1) (k2 : Kept g Q2) {chk : Prog isa}
    (chkCt : RelCT isa (fun s t => (PrivateState g bs1 s ∧ Q1 s) ∧ (PrivateState g bs2 t ∧ Q2 t) ∧ s.sp = t.sp)
      chk (fun _ _ => True))
    (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => (PrivateStart g bs1 s ∧ Q1 s) ∧ (PrivateStart g bs2 t ∧ Q2 t) ∧ s.sp = t.sp)
      (bodyWith v.name v.code chk) (fun _ _ => True) := by
  unfold bodyWith
  apply crt_seq_ct (crtArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (crtArgs_readyQ k1) (crtArgs_readyQ k2)
  exact crt_seq_ct ((crtCall_ct v nb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial))
    (crtCall_readyQ v k1) (crtCall_readyQ v k2) chkCt

theorem privateCheck_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivateState g bs1 s ∧ True) ∧ (PrivateState g bs2 t ∧ True) ∧ s.sp = t.sp)
      (check v.pcName v.pc v.pdName v.pd) (fun _ _ => True) :=
  privateCheckWith_ct v (kept_true g) (kept_true g)
    ((pcCall_ct v nb).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => pcCall_ready v s h.1) (fun s h => pcCall_ready v s h.1) nb eb

theorem privateBody_ct (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivateStart g bs1 s ∧ PrivateStart g bs2 t ∧ s.sp = t.sp)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (fun _ _ => True) :=
  (privateBodyWith_ct v (kept_true g) (kept_true g) (privateCheck_ct v nb eb) nb).mono
    (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2.1, trivial⟩, h.2.2⟩) (fun _ _ _ => trivial)
end VG.Proof.Rsa.Arm
