module

import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExportStateCT
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-! # Move to the second half of the RSA precomputation output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt)

theorem exportAdvance_ready (s : State) {base dst : BitVec 32} {len w : Nat}
    (h : ExportState base dst len w (16 * w) s) :
    WP isa (.block precomputeOutAdvance) s
      (IndexedExport base (dst + BitVec.ofNat 32 (8 * w)) len w (8 * w) 4) := by
  have fits := h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
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
