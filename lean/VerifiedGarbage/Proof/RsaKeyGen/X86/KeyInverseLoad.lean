module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInverse
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyZero
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # Load an independent prime-width or two-word inverse workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure InverseLayout (Z n src mo : Nat) : Prop where
  source_bound : src + 4 * n ≤ Z
  modulus_bound : mo + 4 * n ≤ Z
  source_outside : src + 4 * n ≤ hdr ∨ arr n 15 ≤ src
  modulus_outside : mo + 4 * n ≤ hdr ∨ arr n 15 ≤ mo

theorem inverseLoad_ok {s : State} {B : Addr} {Z n src mo : Nat}
    (h : Ws s B Z n 15) (L : InverseLayout Z n src mo) :
    WP isa (inverseLoad n src mo) s fun t =>
      Ws t B Z n 15 ∧ Outside B hdr (4 * (15 * (n + 2))) s.mem t.mem ∧
      num t.mem B n 0 = val32 s.mem B src n ∧ num t.mem B n aM = val32 s.mem B mo n ∧
      (∀ j, j < 15 → j ≠ 0 → j ≠ aM → num t.mem B n j = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := h.workspace.nowrap
  have f0 := h.arr_fit (j := 0) (by decide)
  have fm := h.arr_fit (j := aM) (by decide)
  have srcBound := L.source_bound
  have moBound := L.modulus_bound
  have srcSep := L.source_outside
  have moSep := L.modulus_outside
  have sepSource : arr n 0 = src ∨ arr n 0 + 4 * n ≤ src ∨ src + 4 * n ≤ arr n 0 := by
    simp only [arr, S, aM] at *
    omega_arith
  have sepModulus : arr n aM = mo ∨ arr n aM + 4 * n ≤ mo ∨ mo + 4 * n ≤ arr n aM := by
    simp only [arr, S, aM] at *
    omega_arith
  unfold inverseLoad seqs
  refine WP.seq (WP.mono (zero_arrays h (by decide)) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have zeros (j : Nat) (hj : j < 15) : num u.mem B n j = 0 := by
    have H := zero j hj
    rw [val32_append] at H
    change val32 u.mem B (arr n j) n = 0
    omega_arith
  have source : val32 u.mem B src n = val32 s.mem B src n :=
    Ou.val32 (by simp only [arr, S] at srcSep; omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hu.workspace h.wpos srcBound
    (by change arr n 0 + 4 * n ≤ Z; unfold S at f0; omega_arith) sepSource)
    fun v ⟨Ov, input, Kv⟩ => ?_)
  change Outside B (arr n 0) (4 * n) u.mem v.mem at Ov
  change num v.mem B n 0 = val32 u.mem B src n at input
  have hv := hu.rest Kv
  have vKeep : Keep B n [0] [] u.mem v.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ov) (by unfold S; omega_arith) (by simp)
  have vFrame : Outside B hdr (4 * (15 * (n + 2))) s.mem v.mem :=
    Ou.trans (Ov.mono (by change hdr ≤ arr n 0; unfold arr; omega_arith)
      (by change arr n 0 + 4 * n ≤ hdr + 4 * (15 * (n + 2)); unfold arr S; omega_arith))
  have modulus : val32 v.mem B mo n = val32 s.mem B mo n :=
    vFrame.val32 (by simp only [arr, S] at moSep; omega_arith) (by omega_arith)
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok hv.workspace h.wpos moBound
    (by change arr n aM + 4 * n ≤ Z; unfold S at fm; omega_arith) sepModulus)
    fun t ⟨Ot, valueM, Kt⟩ => ?_
  change Outside B (arr n aM) (4 * n) v.mem t.mem at Ot
  change num t.mem B n aM = val32 v.mem B mo n at valueM
  have tKeep : Keep B n [aM] [] v.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ot) (by unfold S; omega_arith) (by simp)
  refine ⟨hv.rest Kt, vFrame.trans (Ot.mono (by change hdr ≤ arr n aM; unfold arr; omega_arith)
    (by change arr n aM + 4 * n ≤ hdr + 4 * (15 * (n + 2)); unfold arr S aM; omega_arith)), ?_, valueM.trans modulus, ?_,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · rw [tKeep.num (by decide) (by simp) (h.fit64 (by decide)), input, source]
  · intro j hj j0 jm
    rw [tKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm jm) (by simp) (h.fit64 hj),
      vKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm j0) (by simp) (h.fit64 hj),
      zeros j hj]

end VG.Proof.RsaKeyGen.X86.Key
