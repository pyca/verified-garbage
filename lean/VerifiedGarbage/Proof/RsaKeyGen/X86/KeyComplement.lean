module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPairSubtract
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Form the public-exponent complement from the tiny inverse coefficient -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem complement_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (less : val32 s.mem B (arr 2 3) 2 < val32 s.mem B kEv 2) :
    WP isa (complement n) s fun t =>
      Ws t B Z n 32 ∧ Outside B (arr n aDen) (S n) s.mem t.mem ∧
      val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      num t.mem B n aDen = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fit := h.arr_fit (j := aDen) (by decide)
  have fits := h.fits
  have hn := h.workspace.nowrap
  have eBound : kEv + 8 ≤ Z := by have := h.hdr_le; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_arith
  have xBound : arr 2 3 + 8 ≤ Z := by unfold arr S VG.Impl.Rsa.X86.Keys.hdr at fits ⊢; omega_arith
  have beforeE : kEv + 8 ≤ arr n aDen := by unfold arr S kEv aDen VG.Impl.Rsa.X86.Keys.hdr; omega_arith
  have beforeX : arr 2 3 + 8 ≤ arr n aDen := by unfold arr S aDen VG.Impl.Rsa.X86.Keys.hdr; omega_arith
  unfold complement
  refine WP.seq (WP.mono (zerosW_ok h.workspace (by omega_arith)
    (by change arr n aDen + 4 * (n + 2) ≤ Z; exact fit)) fun u ⟨Ou, zero, Ku⟩ => ?_)
  change Outside B (arr n aDen) (4 * (n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (arr n aDen) (n + 2) = 0 at zero
  have hu := h.rest Ku
  have E : val32 u.mem B kEv 2 = val32 s.mem B kEv 2 := Ou.val32 (Or.inl beforeE) (by omega_arith)
  have X : val32 u.mem B (arr 2 3) 2 = val32 s.mem B (arr 2 3) 2 := Ou.val32 (Or.inl beforeX) (by omega_arith)
  refine WP.mono (subtractPair_ok hu.workspace eBound xBound
    (by change arr n aDen + 8 ≤ Z; unfold S at fit; omega_arith)) fun t ⟨Ot, ⟨borrow, value⟩, Kt⟩ => ?_
  change Outside B (arr n aDen) 8 u.mem t.mem at Ot
  change val32 t.mem B (arr n aDen) 2 + val32 u.mem B (arr 2 3) 2 =
    val32 u.mem B kEv 2 + 2 ^ 64 * borrow.toNat at value
  rw [E, X] at value
  have noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n aDen) 2) (Bool.toNat_le borrow)).mpr
    (Nat.le_of_lt less)
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  have result : val32 t.mem B (arr n aDen) 2 = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by omega_arith
  have high : val32 u.mem B (arr n aDen + 8) n = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 2) (c := n) (by omega_arith)
  have highT : val32 t.mem B (arr n aDen + 8) n = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by unfold S at fit; omega_arith), high]
  have full : val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by
    rw [show n + 2 = 2 + n by omega_arith, val32_append, highT, Nat.mul_zero, Nat.add_zero, result]
  have bound : val32 t.mem B (arr n aDen) (n + 2) < 2 ^ (32 * n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (val32_lt s.mem B kEv 2))
      (Nat.pow_le_pow_right (by decide) (by omega_arith))
  exact ⟨hu.rest Kt, Ou.trans (Ot.mono (Nat.le_refl _) (by omega_arith)), full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_arith : n ≤ n + 2) bound).trans full,
    Ku.trans (Kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.Key
