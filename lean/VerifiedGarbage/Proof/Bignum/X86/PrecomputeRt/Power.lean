module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Double
public import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn

/-! # The inverse of the precomputation at a run-time width

`-M⁻¹ mod 2³²` at 152 (`inverse_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputeFn

theorem inverse_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (hodd : val32 s.mem base numOff (nw len) % 2 = 1) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) s fun t =>
      (val32 s.mem base numOff (nw len) * w32 t.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Outside base invOff 4 s.mem t.mem ∧ Keeps clob s t := by
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  rw [n0] at f0
  have b264 : 264 ≤ bytes := by have := dims.1; simp only [wb] at f0; omega_using [f0, dims]
  obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega_using [dims]⟩
  have hodd' : w32 s.mem base numOff % 2 = 1 := by
    rw [hk, VG.Proof.Mont.X86.Dynamic.val32_parity] at hodd; exact hodd
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h.scratch (mo := numOff) (inv := invOff)
    (by simp only [numOff]; omega_using [b264]) (by simp only [invOff]; omega_using [f0]) hodd') fun t ⟨I, O, K⟩ => ⟨?_, O, K⟩
  rw [hk, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
  exact I

end VG.Proof.Bignum.X86.PrecomputeRt
