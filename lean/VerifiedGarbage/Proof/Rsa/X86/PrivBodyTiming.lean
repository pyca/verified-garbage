module
public import VerifiedGarbage.Proof.Rsa.X86.PrivStages
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Rsa.X86.PrivCallsTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivTailContext
import VerifiedGarbage.Proof.Rsa.X86.PrivTailTiming

/-! # The complete private body has equal traces for independent private components -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked

theorem privateCheck_relCT (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivateState g bs1 s ∧ PrivateState g bs2 t)
      (check v.pcName v.pc v.pdName v.pd) (fun _ _ => True) := by
  unfold check
  apply pair_seq_ct (precomputeArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.context.sp.trans h.2.context.sp.symm)) (fun _ _ _ => trivial))
    (fun s h => pcArgs_ready s h) (fun s h => pcArgs_ready s h)
  apply pair_seq_ct (pcCall_ct v nb) (fun s h => pcCall_ready v s h) (fun s h => pcCall_ready v s h)
  apply pair_seq_ct (publicArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.context.sp.trans h.2.context.sp.symm)) (fun _ _ _ => trivial))
    (fun s h => pdArgs_ready s h) (fun s h => pdArgs_ready s h)
  apply pair_seq_ct (pdCall_ct v nb eb) (fun s h => pdCall_ready v s h) (fun s h => pdCall_ready v s h)
  exact tail_relCT.mono (fun _ _ h => ⟨h.1.context.tailInput,
    h.2.context.tailInput, h.1.context.sp.trans h.2.context.sp.symm⟩) (fun _ _ _ => trivial)

theorem privateBody_relCT (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivateState g bs1 s ∧ PrivateState g bs2 t)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (crtArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.context.sp.trans h.2.context.sp.symm)) (fun _ _ _ => trivial))
    (fun s h => crtArgs_ready s h) (fun s h => crtArgs_ready s h)
  exact pair_seq_ct (crtCall_ct v nb) (fun s h => crtCall_ready v s h) (fun s h => crtCall_ready v s h)
    (privateCheck_relCT v nb eb)

end VG.Proof.Rsa.X86.PrivChecked
