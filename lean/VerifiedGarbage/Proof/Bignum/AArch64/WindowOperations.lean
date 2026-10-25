module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle

import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawSquare
import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawProduct
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem square_ok {s : State} {B : Addr} {Z w a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (haN : a ≠ aN)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.square a) s fun t =>
      wv t.mem B (slot w a) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,a] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega_arith
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.square
  refine WP.seq (WP.mono (WindowRaw.raw_width_ok hs h0 hH hZ hw hw' hmod ha ha1 ha2)
    fun u ⟨hu,ho,h8,h12,h7,ku⟩ => ?_)
  have hHU := (Square.scratch_arrays ho).hdr hH
  have hN : wv u.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho.wv (by omega_arith) (by omega_arith)
  have hi : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0 := by
    rw [ho.word (d := slot w aN) (by omega_arith) (by omega_arith)]; exact hinv
  refine WP.mono (lazy_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    hHU hZ hw hw' hmod h8 h12 h7 ha ha1 ha2 haN hi) fun t ⟨ht,hf,kt⟩ => ?_
  rw [hu,hN] at ht
  exact ⟨ht,((Square.scratch_arrays ho).mono (by simp)).trans hf,(ku.trans kt).mono (by decide)⟩

theorem product_ok {s : State} {B : Addr} {Z w o a b : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (hoN : o ≠ aN)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb : b < 8) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.product o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,o] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega_arith
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.product
  refine WP.seq (WP.mono (WindowRaw.product_width_ok hs h0 hH hZ hw hw' hmod ha hb ha1 ha2 hb1 hb2)
    fun u ⟨hu,hout,h8,h12,h7,ku⟩ => ?_)
  have hHU := (Square.scratch_arrays hout).hdr hH
  have hN : wv u.mem B (slot w aN) w = wv s.mem B (slot w aN) w := hout.wv (by omega_arith) (by omega_arith)
  have hi : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0 := by
    rw [hout.word (d := slot w aN) (by omega_arith) (by omega_arith)]; exact hinv
  have hprod : wv u.mem B (slot w aAcc+16) (2*w) < wv u.mem B (slot w aN) w * 2^(64*w) := by
    rw [hu,hN,Nat.mul_comm (wv s.mem B (slot w a) w)]
    exact Nat.mul_lt_mul'' hB (wv_lt _ _ _ _)
  refine WP.mono (canonical_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    hHU hZ hw hw' hmod h8 h12 h7 ho ho1 ho2 hoN hi (by rw [hN]; omega_arith) hprod)
    fun t ⟨hlt,ht,hf,kt⟩ => ?_
  rw [hu,hN] at ht
  rw [hN] at hlt
  exact ⟨hlt,ht,((Square.scratch_arrays hout).mono (by simp)).trans hf,(ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowArithmetic
