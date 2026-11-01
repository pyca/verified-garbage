module

public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
public import VerifiedGarbage.Proof.Bignum.Arm.ExportState
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT

import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Move to the second half of the RSA precomputation output -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExportStateCT.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)

theorem exportAdvance_ready (s : State) {base dst : BitVec 32} {len w : Nat}
    (h : ExportState base dst len w (16 * w) s) :
    WP isa (.block precomputeOutAdvance) s
      (IndexedExport base (dst + BitVec.ofNat 32 (8 * w)) len w (8 * w) 4) := by
  have fits := h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have dstFit := h.fits
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (precomputeOutAdvance_ok s h.workspace (by omega) h.ptr header.count) ?_
  rintro t ⟨output, index, mem, rest⟩
  have addr : State.addr (dst + BitVec.ofNat 32 (8 * w)) = off (State.addr dst) (8 * w) := addr_add (by omega)
  have val : (dst + BitVec.ofNat 32 (8 * w)).toNat = dst.toNat + 8 * w := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * w < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : dst.toNat + 8 * w < 2 ^ 32)]
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr,
    by rw [output, h.output], by omega, by rw [val]; omega, ?_, ?_⟩, index⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.wr, addr]; exact CallLay.inRegions_sub h.write (by omega) (by omega)
  · rw [addr]; exact h.separate.sub_right (Offset.sub_base _ (by omega))

end VG.Proof.Bignum.Arm
