module

public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Public slices of a writable FFDH output. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem OutputBuffer.prefix {dst : BitVec 32} {n k : Nat} {s : State}
    (h : OutputBuffer dst k s) (fit : n ≤ k) : OutputBuffer dst n s := by
  refine ⟨by have := h.fits; omega, ?_⟩
  obtain ⟨r, hr, hc⟩ := h.writable
  exact ⟨r, hr, by unfold Region.Contains at *; omega⟩

theorem OutputBuffer.slice {dst : BitVec 32} {n k d : Nat} {s : State}
    (h : OutputBuffer dst k s) (positive : 0 < n) (fit : d + n ≤ k) :
    OutputBuffer (dst + BitVec.ofNat 32 d) n s := by
  have ptr : (dst + BitVec.ofNat 32 d).toNat = dst.toNat + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.fits; omega),
      Nat.mod_eq_of_lt (by have := h.fits; omega)]
  refine ⟨by rw [ptr]; have := h.fits; omega, ?_⟩
  rw [VG.Arm.addr_add (by have := h.fits; omega)]
  exact CallLay.inRegions_sub h.writable fit (by have := h.fits; omega)

end VG.Proof.Ffdh.Arm
