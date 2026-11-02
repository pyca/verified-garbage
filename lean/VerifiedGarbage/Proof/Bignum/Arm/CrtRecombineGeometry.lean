module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductGeometry
public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineProduct

import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # The extended product buffers contain every possible CRT reconstruction -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

theorem crt_wideSum_fits {a b c w : Nat} (ha : a < 2 ^ (64 * w))
    (hb : b < 2 ^ (64 * w)) (hc : c < 2 ^ (64 * w)) :
    a * b + c < 2 ^ (32 * (4 * w + 2)) := by
  let R := 2 ^ (64 * w)
  have positive : 0 < R := Nat.two_pow_pos _
  have product : a * b ≤ R * R := Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hb)
  have square : R ≤ R * R := by
    have := Nat.mul_le_mul_left R (by omega : 1 ≤ R)
    simpa only [Nat.mul_one] using this
  have twice : R * R + R * R ≤ R * R * 2 ^ 64 := by
    have := Nat.mul_le_mul_left (R * R) (by decide : 2 ≤ 2 ^ 64)
    simpa only [Nat.mul_two] using this
  have bound : a * b + c < R * R * 2 ^ 64 := by omega
  simpa only [show 32 * (4 * w + 2) = (64 * w + 64 * w) + 64 by omega, Nat.pow_add] using bound

theorem CrtShared.recombine_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    CrtRecombineInput g.base g.size (workspaceWords g.words) g.words (productOffset g.words)
      (crtProductA g.words true) (crtProductB g.words) (pOffset g.words) (qOffset g.words) (modulusOffset g.words) s := by
  have size := h.buffers.storageFits
  have fits : modulusOffset g.words + 4 * (4 * g.words + 2) ≤ g.size := Nat.le_trans (crt_modulus_end_le _) size
  have sep : productOffset g.words + 4 * (4 * g.words + 2) ≤ modulusOffset g.words := by
    simp only [modulusOffset, compareOffset, productBytes, productWords]; omega
  refine ⟨h.product_input ready true, h.pad_input ready,
    ⟨h.buffers.workspace.nowrap, by omega, by omega, Or.inl (by omega), h.buffers.workspace.writable⟩,
    by simp only [productOffset, stride]; omega, sep, ?_⟩
  apply crt_wideSum_fits
  · simpa only [show 32 * (2 * g.words) = 64 * g.words by omega] using
      val32_lt s.mem (State.addr g.base) (crtProductA g.words true) (2 * g.words)
  · simpa only [show 32 * (2 * g.words) = 64 * g.words by omega] using
      val32_lt s.mem (State.addr g.base) (crtProductB g.words) (2 * g.words)
  · rw [numAt_native]
    simpa only [show 32 * (2 * g.words) = 64 * g.words by omega] using
      val32_lt s.mem (State.addr g.base) (Proof.Rsa.Mont.arrAt g.words 1) (2 * g.words)

end VG.Proof.Bignum.Arm
