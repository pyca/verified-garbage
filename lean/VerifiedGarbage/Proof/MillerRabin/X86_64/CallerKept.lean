module

import VerifiedGarbage.Proof.MillerRabin.Keeps
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerSave
public import VerifiedGarbage.Proof.MillerRabin.Contract

/-! # Recover the caller's header and padding after the prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.Proof.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem kept_header {B : Addr} {n w j : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m m')
    (hn : 32 ≤ n) (hj : j < 32) (he : j ∉ [22, 26, 27, 28, 31]) :
    word m' B (8 * j) = word m B (8 * j) := by
  apply keeps_word h (by omega_arith)
  · intro k hk
    have hne : j ≠ k := fun hEq => he (hEq ▸ hk)
    omega_arith
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl) <;>
      left <;> simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_arith
  · left
    simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_arith

theorem kept_padding {B : Addr} {n w : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m m')
    (hn : pad w + 8 ≤ 8 * n) :
    word m' B (pad w) = word m B (pad w) := by
  apply keeps_word h hn
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl) <;>
      right <;> simp only [pad, slot, hdrBytes, aR1] <;> omega_arith
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl)
    all_goals right
    all_goals simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, pad, slot, hdrBytes, aR1]
    all_goals omega_arith
  · right
    simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      pad, slot, hdrBytes, aR1]
    omega_arith

end VG.Proof.MillerRabin.X86_64.Caller
