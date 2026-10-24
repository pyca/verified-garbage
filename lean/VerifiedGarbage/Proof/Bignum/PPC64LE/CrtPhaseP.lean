module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerB
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: a prime's phase

`phaseP_ok`: `setupP` and `power`, the input to the power of the prime's
exponent modulo the prime, in its working space's array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The low words of a number below their range. -/
theorem wv_low {m : Mem} {B : Addr} {d wA wX v : Nat} (h : wv m B d wX = v) (hv : v < 2 ^ (64 * wA))
    (hw : wA ≤ wX) : wv m B d wA = v := by
  have hs := wv_add m B d wA (wX - wA)
  rw [show wA + (wX - wA) = wX by omega, h] at hs
  have hl := wv_lt m B d wA
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * wA) (wX - wA)) with h0 | h0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at hs; exact hs.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * wA)) h0
    omega

/-- `setupP oB oLen` and `power xj oD oLen`: for the prime `P` in `X`'s array
`xj` (below `2^(64 w_A)`, `w_A` the words of its length `L`), its working
space at `off BX oA` (the header's word `oB`) holds `P` in array 0 and
`c^d mod P` in array 4. -/
theorem phaseP_ok {s : State} {BX I D : Addr} {Z oA wX xj k L Pv oB oLen oD : Nat}
    (hs : Scr s BX Z) (hA : oA + slot (wsWords L) 8 ≤ Z) (hXA : slot wX 8 ≤ oA)
    (hwx : wsWords L ≤ wX) (hwX : wX < 2 ^ 31) (hxj : xj < 8)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0)
    (hB : word s.mem BX oB = off BX oA) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L)
    (hI : word s.mem BX oIn = off I 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hDp : word s.mem BX oD = off D 0) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) (hk : 1 ≤ k) (hk' : k < 2 ^ 63)
    (hrdI : ∀ i < k, InRegions (s.rd ++ s.wr) (off I i) 1) (hsepI : ∀ i < k, ∀ x, ofs BX x < Z → off I i ≠ x)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : Mont.val32 s.mem BX (slot wX xj) (2 * wX) = Pv) (hPb : Pv < 2 ^ (64 * wsWords L)) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) :
    WP isa (.seq (.block (setupP oB oLen)) (power xj oD oLen)) s fun t =>
      (Mont.val32 t.mem (off BX oA) (slot (wsWords L) 0) (2 * wsWords L) = Pv ∧
        Mont.val32 t.mem (off BX oA) (slot (wsWords L) 4) (2 * wsWords L) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem I k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot (wsWords L) 8) s.mem t.mem ∧
        t.gpr .r10 = off (off BX oA) (slot (wsWords L) 0) ∧ t.gpr .r21 = off (off BX oA) (slot (wsWords L) 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (wsWords L + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords L)) ∧
      Keep (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs) s t := by
  have hn := hs.nowrap
  have e8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hw2 : 2 ≤ wsWords L := by unfold wsWords; omega
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL (by omega) hB hLw hL hL')
    fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  refine WP.mono (power_ok (I := I) (D := D) (k := k) (L := L) (hs.congr k1.wr) hA hXA hw2 (by omega) hwx hxj
    a10 a29 a11 ((k1.gpr _ (by decide)).trans h23) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) (by rw [m1]; exact hI) (by rw [m1]; exact hK) hk hk'
    (fun i hi => by rw [k1.rd, k1.wr]; exact hrdI i hi) hsepI hoD hoL (by rw [m1]; exact hDp)
    (by rw [m1]; exact hLw) hL (by omega) (fun i hi => by rw [k1.rd, k1.wr]; exact hrdD i hi) hsepD
    (by rw [m1]; exact wv_low (by rw [← Pre.val32_eq_wv]; exact hP) hPb hwx) hP2 hPodd)
    fun t ⟨⟨v0, v4, o⟩, k2⟩ => ⟨⟨v0, by rw [v4, m1], by rw [← m1]; exact o, (k2.gpr _ (by decide)).trans a10,
      (k2.gpr _ (by decide)).trans a21, (k2.gpr _ (by decide)).trans a29, (k2.gpr _ (by decide)).trans a11⟩,
      (k1.trans k2).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt
