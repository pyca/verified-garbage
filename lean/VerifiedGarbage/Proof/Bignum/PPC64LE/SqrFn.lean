module

import VerifiedGarbage.Proof.Bignum.PPC64LE.SqrCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontSqr
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios

/-!
# Montgomery squaring on PPC64LE: `vg_rsa_mont_mul`'s state

`sqr_P`: `sqrTail` from `MontFn.lean`'s `P3`, as `tail_P`, for `a = b`
other than array 3.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.MontSqr

theorem sqr_P {d : FnData} {s : State} (h : P3 d s) (hab : d.a = d.b) (ha3 : d.a ≠ 3) :
    WP isa sqrTail s fun t =>
      (val32 t.mem d.B (slot d.w d.o) (2 * d.w) < val32 s.mem d.B (slot d.w 0) (2 * d.w) ∧
        val32 t.mem d.B (slot d.w d.o) (2 * d.w) * 2 ^ (64 * d.w) % val32 s.mem d.B (slot d.w 0) (2 * d.w) =
          val32 s.mem d.B (slot d.w d.a) (2 * d.w) * val32 s.mem d.B (slot d.w d.b) (2 * d.w) %
            val32 s.mem d.B (slot d.w 0) (2 * d.w) ∧
        Outs d.B [(slot d.w 2, 8 * (d.w + 2)), (slot d.w 3, 8 * (d.w + 2)),
          (slot d.w d.o, 8 * (d.w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  obtain ⟨hm, h5, h6, -, h8, h9, h10, h11, h4, h12, -⟩ := h
  rw [← hab]
  exact Sqr.sqrN_ok hm.scr (by decide) hm.ho hm.ha hm.ho2 hm.ho3 hm.ha2 ha3 hm.w2 hm.w31 hm.hZ h5 h6 h8 h9 h10
    h11 h4 (by rw [h12]; exact (s.mem.readW _ 32).isLt) (by rw [h12]; exact hm.hinv) (by rw [hab]; exact hm.hB)

end VG.Proof.Bignum.PPC64LE
