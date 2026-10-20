module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportResidueCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportFinalResidue
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry

/-! # Reconstruct the wide CRT result without leaking its inputs -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_recombineStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) recombine) (fun _ _ => True) := by
  have transfer : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq (.block CrtFn.qSource) (transferArray 1 6)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_importResidue_ct h.1.1.buffers.context.sepMQ.symm s t tr1 tr2 u v h e1 e2
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s (CrtSelected g bs g.base) :=
    (crt_importFinalResidue_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have recombination : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      recombine (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_recombine_ct (h.1.1.compare_input h.1.2).fit s t tr1 tr2 u v
      ⟨h.1.1.recombine_input h.1.2, h.2.1.1.recombine_input h.2.1.2, h.2.2⟩ e1 e2
  exact crt_seq_ct transfer (fun s h => wp s h) (fun s h => wp s h) recombination

end VG.Proof.Bignum.Arm
