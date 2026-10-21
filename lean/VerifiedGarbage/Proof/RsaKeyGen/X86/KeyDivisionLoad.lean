module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionClear
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # Load the native division bank without clearing its temporary arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure DivisionInputs (Z n src divisor : Nat) : Prop where
  source_bound : src + 4 * n ≤ Z
  divisor_bound : divisor + 4 * n ≤ Z
  source_outside : src + 4 * n ≤ hdr ∨ arr n 4 ≤ src
  divisor_outside : divisor + 4 * n ≤ hdr ∨ arr n 4 ≤ divisor

theorem divisionLoad_ok {s : State} {B : Addr} {Z n src divisor : Nat}
    (h : Ws s B Z n 4) (L : DivisionInputs Z n src divisor) :
    WP isa (divisionLoad n src divisor) s fun t =>
      Ws t B Z n 4 ∧ Outside B hdr (4 * (4 * (n + 2))) s.mem t.mem ∧
      (divisionGeometry B Z n).value t.mem 0 = val32 s.mem B src n ∧
      (divisionGeometry B Z n).value t.mem 2 = val32 s.mem B divisor n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := h.workspace.nowrap
  have f0 := h.arr_fit (j := 0) (by decide)
  have f2 := h.arr_fit (j := 2) (by decide)
  have srcBound := L.source_bound
  have divBound := L.divisor_bound
  have srcSep := L.source_outside
  have divSep := L.divisor_outside
  have sepSource : arr n 0 = src ∨ arr n 0 + 4 * n ≤ src ∨ src + 4 * n ≤ arr n 0 := by
    simp only [arr, S] at *
    omega
  have sepDivisor : arr n 2 = divisor ∨ arr n 2 + 4 * n ≤ divisor ∨ divisor + 4 * n ≤ arr n 2 := by
    simp only [arr, S] at *
    omega
  unfold divisionLoad seqs
  refine WP.seq (WP.mono (division_clear h) fun u ⟨hu, Ou, topU, Ku⟩ => ?_)
  have uFrame : Outside B hdr (4 * (4 * (n + 2))) s.mem u.mem :=
    Ou.mono (by unfold arr; omega) (by unfold arr S; omega)
  have source : val32 u.mem B src n = val32 s.mem B src n :=
    uFrame.val32 (by simp only [arr, S] at srcSep; omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hu.workspace h.wpos srcBound
    (by change arr n 0 + 4 * n ≤ Z; unfold S at f0; omega) sepSource)
    fun v ⟨Ov, input, Kv⟩ => ?_)
  change Outside B (arr n 0) (4 * n) u.mem v.mem at Ov
  change val32 v.mem B (arr n 0) n = val32 u.mem B src n at input
  have hv := hu.rest Kv
  have vFrame : Outside B hdr (4 * (4 * (n + 2))) s.mem v.mem :=
    uFrame.trans (Ov.mono (by unfold arr; omega) (by unfold arr S; omega))
  have topV : w32 v.mem B (arr n 2 + 4 * n) = 0 := by
    rw [Ov.w32 (by unfold arr S; omega) (by unfold S at f2; omega), topU]
  have modulus : val32 v.mem B divisor n = val32 s.mem B divisor n :=
    vFrame.val32 (by simp only [arr, S] at divSep; omega) (by omega)
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hv.workspace h.wpos divBound
    (by change arr n 2 + 4 * n ≤ Z; unfold S at f2; omega) sepDivisor)
    fun t ⟨Ot, valueD, Kt⟩ => ?_
  change Outside B (arr n 2) (4 * n) v.mem t.mem at Ot
  change val32 t.mem B (arr n 2) n = val32 v.mem B divisor n at valueD
  have topT : w32 t.mem B (arr n 2 + 4 * n) = 0 := by
    rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by unfold S at f2; omega), topV]
  refine ⟨hv.rest Kt, vFrame.trans (Ot.mono (by unfold arr; omega) (by unfold arr S; omega)), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · change val32 t.mem B (arr n 0) n = _
    rw [Ot.val32 (by unfold arr S; omega) (by unfold S at f0; omega), input, source]
  · change val32 t.mem B (arr n 2) (n + 1) = _
    rw [val32_succ, topT, Nat.mul_zero, Nat.add_zero, valueD, modulus]

end VG.Proof.RsaKeyGen.X86.Key
