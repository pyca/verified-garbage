module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math

/-! # Correctness of DSA's AArch64 byte-reduction arithmetic -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Horner reduction's arithmetic step, using any verified Montgomery
backend. The modulus can be composite. The byte is represented by array 1;
array 4 holds 256R mod m and is preserved. -/
theorem reduceStep_ok (M : Mont) {s : State} {B : Addr} {Z w m y byte : Nat}
    {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hn : wv s.mem B (slot w aN) w = m) (hm : m % 2 = 1)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hy : wv s.mem B (slot w aY) w = y) (hyl : y < m)
    (hb : wv s.mem B (slot w aX) w = byte) (hbyte : byte < m)
    (hc : wv s.mem B (slot w aXm) w = 256 * 2 ^ (64 * w) % m) :
    WP isa (VG.Impl.Dsa.AArch64.Arithmetic.reduceStep M.mm) s fun t =>
      Good t B Z w minv ∧
      wv t.mem B (slot w aY) w = (256 * y + byte) % m ∧
      Arrays B w [aAcc, aTmp, aY] s.mem t.mem ∧ Keep mmRegs s t := by
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by
    have := hg.scr.nowrap
    omega
  unfold VG.Impl.Dsa.AArch64.Arithmetic.reduceStep
  refine WP.seq (WP.mono (M.mm_ok hg hZ hw hw' (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hinv ?_) fun u h => ?_)
  · rw [hy, hn]
    exact hyl
  obtain ⟨hu, hlu, hmu, hfu, hku⟩ := h
  have un : wv u.mem B (slot w aN) w = m :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hn
  have ub : wv u.mem B (slot w aX) w = byte :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hb
  rw [hn, hy, hc, Nat.mul_comm (256 * 2 ^ (64 * w) % m) y] at hmu
  rw [hn] at hlu
  have uy := VG.Proof.Dsa.mont_scale (coprime_pow2 hm (64 * w)) hmu
  rw [Nat.mod_eq_of_lt hlu, Nat.mul_comm y 256] at uy
  refine WP.mono (addMod_ok hu.scr hu.x0 hu.hdr hZ hw hw'
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [un]; exact hlu) (by rw [ub, un]; exact hbyte)) fun t ht => ?_
  obtain ⟨hv, hf, hk⟩ := ht
  refine ⟨⟨hu.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hu.x0, hf.hdr hu.hdr⟩,
    ?_, hfu.trans hf, (hku.trans hk).mono (by decide)⟩
  rw [uy, ub, un] at hv
  rw [hv, Nat.mod_add_mod]

end VG.Proof.Dsa.AArch64
