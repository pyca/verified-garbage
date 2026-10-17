module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishSelection
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtOutputArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMaskedCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Reconstruction and masked output hide both the result and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_finishStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtFinishSelection g bs1 s ∧ CrtFinishSelection g bs2 t ∧ s.sp = t.sp)
      CrtFn.finish (fun _ _ => True) := by
  have reconstruct : RelCT isa (fun s t => CrtFinishSelection g bs1 s ∧ CrtFinishSelection g bs2 t ∧ s.sp = t.sp)
      (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) VG.Impl.Bignum.Arm.Crt.recombine) (fun _ _ => True) :=
    crt_recombineStage_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have args : RelCT isa (fun s t => CrtExportSelection g bs1 s ∧ CrtExportSelection g bs2 t ∧ s.sp = t.sp)
      (.block CrtFn.outputArgs) (fun _ _ => True) :=
    crt_outputArgs_ct.mono (fun _ _ h => ⟨h.1.1.2.ptr.trans h.2.1.1.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  exact (crt_seq_ct reconstruct (fun s h => crt_recombineExport_ready s h)
    (fun s h => crt_recombineExport_ready s h)
    (crt_seq_ct args (fun s h => crt_exportArgs_ready s h) (fun s h => crt_exportArgs_ready s h) exportBufferMasked_ct)).assoc.assoc

end VG.Proof.Bignum.Arm
