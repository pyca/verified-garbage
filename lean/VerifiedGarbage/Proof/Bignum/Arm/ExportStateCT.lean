module

public import VerifiedGarbage.Proof.Bignum.Arm.ExportState
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Array export preserves the public state needed by the next export -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def IndexedExport (base dst : BitVec 32) (len w capacity o : Nat) (s : State) : Prop :=
  ExportState base dst len w capacity s ∧ s.gpr .r2 = BitVec.ofNat 32 o

theorem IndexedExport.small {base dst : BitVec 32} {len w capacity o : Nat} {s : State}
    (h : IndexedExport base dst len w capacity o s) : SmallFnReady base len w o s :=
  ⟨h.1.workspace, h.1.layout, h.1.width, h.1.ptr, h.2⟩

theorem exportArray_indexed_ct {base dst : BitVec 32} {len w capacity o : Nat} (ho : o < 8) :
    RelCT isa (fun s t => IndexedExport base dst len w capacity o s ∧ IndexedExport base dst len w capacity o t)
      exportArray (fun s t => ExportState base dst len w capacity s ∧ ExportState base dst len w capacity t) := by
  have ct := (exportArray_ct (base := base) (dst := dst) (len := len) (w := w) ho).mono
    (P' := fun s t => IndexedExport base dst len w capacity o s ∧ IndexedExport base dst len w capacity o t)
    (fun _ _ h => ⟨h.1.small, h.2.small, h.1.1.output, h.2.1.output⟩)
    (fun _ _ h => h)
  exact (ct.wp (fun s t h => ⟨exportArray_state s h.1.1 ho h.1.2,
    exportArray_state t h.2.1 ho h.2.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Bignum.Arm
