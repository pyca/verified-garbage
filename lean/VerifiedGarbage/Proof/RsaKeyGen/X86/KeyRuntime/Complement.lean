module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PairSubtract
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Form the public-exponent complement from the tiny inverse coefficient -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aDen kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem complement_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (less : val32 s.mem B (arr 2 3) 2 < val32 s.mem B kEv 2) :
    WP isa complement s fun t =>
      Ws t B Z n 32 ∧ Outside B (arr n aDen) (S n) s.mem t.mem ∧
      val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      num t.mem B n aDen = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit (j := aDen) (by decide)
  have fits := h.old.fits
  have hn := h.old.workspace.nowrap
  have eBound : kEv + 8 ≤ Z := by have := h.hdr_le; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega
  have xBound : arr 2 3 + 8 ≤ Z := by unfold arr S VG.Impl.Rsa.X86.Keys.hdr at fits ⊢; omega
  have beforeE : kEv + 8 ≤ arr n aDen := by unfold arr S kEv aDen VG.Impl.Rsa.X86.Keys.hdr; omega
  have beforeX : arr 2 3 + 8 ≤ arr n aDen := by unfold arr S aDen VG.Impl.Rsa.X86.Keys.hdr; omega
  unfold complement
  refine WP.seq (WP.mono (zero_ok h .modulus (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) fit)
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change Outside B (arr n aDen) (4 * (n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (arr n aDen) (n + 2) = 0 at zero
  have E : val32 u.mem B kEv 2 = val32 s.mem B kEv 2 := Ou.val32 (Or.inl beforeE) (by omega)
  have X : val32 u.mem B (arr 2 3) 2 = val32 s.mem B (arr 2 3) 2 := Ou.val32 (Or.inl beforeX) (by omega)
  refine hu.ptr_ok (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) (by decide) (by decide)
    (by simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words]; unfold S at fit; omega)
    fun v Kv mv P => ?_
  have hv := hu.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine WP.mono (subtractPair_ok hv.old.workspace P eBound xBound
    (by change arr n aDen + 8 ≤ Z; unfold S at fit; omega)) fun t ⟨Ot, ⟨borrow, value⟩, Kt⟩ => ?_
  rw [mv] at Ot value
  change Outside B (arr n aDen) 8 u.mem t.mem at Ot
  change val32 t.mem B (arr n aDen) 2 + val32 u.mem B (arr 2 3) 2 =
    val32 u.mem B kEv 2 + 2 ^ 64 * borrow.toNat at value
  rw [E, X] at value
  have noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n aDen) 2) (Bool.toNat_le borrow)).mpr
    (Nat.le_of_lt less)
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  have result : val32 t.mem B (arr n aDen) 2 = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by omega
  have high : val32 u.mem B (arr n aDen + 8) n = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 2) (c := n) (by omega)
  have highT : val32 t.mem B (arr n aDen + 8) n = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by unfold S at fit; omega), high]
  have full : val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by
    rw [show n + 2 = 2 + n by omega, val32_append, highT, Nat.mul_zero, Nat.add_zero, result]
  have bound : val32 t.mem B (arr n aDen) (n + 2) < 2 ^ (32 * n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (val32_lt s.mem B kEv 2))
      (Nat.pow_le_pow_right (by decide) (by omega))
  have frame := Ou.trans (Ot.mono (Nat.le_refl _) (by omega))
  have K : Keeps [.eax, .ecx, .edx, .ebp] s t := Ku.trans
    ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  exact ⟨h.keep K (frame.mono (Nat.zero_le _) (by unfold S at fit; omega)), frame, full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2) bound).trans full,
    K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
