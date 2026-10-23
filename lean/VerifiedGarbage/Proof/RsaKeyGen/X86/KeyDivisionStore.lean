module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Export native division results to persistent workspace arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionOutputs (Z n quotient remainder : Nat) : Prop where
  quotient_bound : quotient + 4 * n ≤ Z
  remainder_bound : remainder + 4 * n ≤ Z
  quotient_outside : quotient + 4 * n ≤ hdr ∨ arr n 4 ≤ quotient
  remainder_outside : remainder + 4 * n ≤ hdr ∨ arr n 4 ≤ remainder
  separate : quotient + 4 * n ≤ remainder ∨ remainder + 4 * n ≤ quotient

theorem divisionStore_ok {s : State} {B : Addr} {Z n quotient remainder : Nat}
    (h : Ws s B Z n 4) (L : DivisionOutputs Z n quotient remainder)
    (bound : (divisionGeometry B Z n).value s.mem 1 < 2 ^ (32 * n)) :
    WP isa (divisionStore n quotient remainder) s fun t =>
      Ws t B Z n 4 ∧ Outs B [(quotient, 4 * n), (remainder, 4 * n)] s.mem t.mem ∧
      val32 t.mem B quotient n = (divisionGeometry B Z n).value s.mem 0 ∧
      val32 t.mem B remainder n = (divisionGeometry B Z n).value s.mem 1 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := h.workspace.nowrap
  have f0 := h.arr_fit (j := 0) (by decide)
  have f1 := h.arr_fit (j := 1) (by decide)
  have qBound := L.quotient_bound
  have rBound := L.remainder_bound
  have qSep := L.quotient_outside
  have rSep := L.remainder_outside
  have sep := L.separate
  have sepQ : quotient = arr n 0 ∨ quotient + 4 * n ≤ arr n 0 ∨ arr n 0 + 4 * n ≤ quotient := by
    simp only [arr, S] at *
    omega_arith
  have sepR : remainder = arr n 1 ∨ remainder + 4 * n ≤ arr n 1 ∨ arr n 1 + 4 * n ≤ remainder := by
    simp only [arr, S] at *
    omega_arith
  have low : val32 s.mem B (arr n 1) n = (divisionGeometry B Z n).value s.mem 1 :=
    VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_arith : n ≤ n + 1) bound
  unfold divisionStore
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok h.workspace h.wpos
    (by change arr n 0 + 4 * n ≤ Z; unfold S at f0; omega_arith) qBound sepQ)
    fun u ⟨Ou, Q, Ku⟩ => ?_)
  have hu := h.rest Ku
  have R : val32 u.mem B (arr n 1) n = (divisionGeometry B Z n).value s.mem 1 := by
    rw [Ou.val32 (by simp only [arr, S] at qSep; unfold arr S; omega_arith)
      (by unfold S at f1; omega_arith), low]
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hu.workspace h.wpos
    (by change arr n 1 + 4 * n ≤ Z; unfold S at f1; omega_arith) rBound sepR)
    fun t ⟨Ot, V, Kt⟩ => ?_
  refine ⟨hu.rest Kt, (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp)), ?_, V.trans R,
    Ku.trans Kt⟩
  rw [Ot.val32 sep (by omega_arith), Q]
  rfl

end VG.Proof.RsaKeyGen.X86.Key
