module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Clear
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Load a prime, exponent or full-width inverse bank without specializing code -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr S)
open VG.Impl.Rsa.X86.Keys (hdr aM)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (InverseLayout)

theorem inverseLoad_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src mo : Loc}
    (h : Ws s B Z n N) (bound : 15 ≤ N) (hw : w ≠ .correction)
    (L : InverseLayout Z (w.words n) (src.offset n) (mo.offset n)) :
    WP isa (inverseLoad w src mo) s fun t =>
      Ws t B Z n N ∧ Outside B hdr (4 * (15 * (w.words n + 2))) s.mem t.mem ∧
      num t.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) ∧
      num t.mem B (w.words n) aM = val32 s.mem B (mo.offset n) (w.words n) ∧
      (∀ j, j < 15 → j ≠ 0 → j ≠ aM → num t.mem B (w.words n) j = 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  have f0 := H.ws.arr_fit (j := 0) (by decide)
  have fm := H.ws.arr_fit (j := aM) (by decide)
  rw [kw_words h.width] at f0 fm
  have srcBound := L.source_bound
  have moBound := L.modulus_bound
  have srcSep := L.source_outside
  have moSep := L.modulus_outside
  have sepSource : (Loc.array w 0).offset n + 4 * w.words n ≤ src.offset n ∨
      src.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n := by
    simp only [offset_array, arr, S] at *
    omega
  have sepModulus : (Loc.array w aM).offset n + 4 * w.words n ≤ mo.offset n ∨
      mo.offset n + 4 * w.words n ≤ (Loc.array w aM).offset n := by
    simp only [offset_array, arr, S, aM] at *
    omega
  unfold inverseLoad VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clear_ok h w hw (by decide) bound) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have zeros (j : Nat) (hj : j < 15) : num u.mem B (w.words n) j = 0 := by
    have V := zero j hj
    rw [offset_array, val32_append] at V
    change val32 u.mem B (arr (w.words n) j) (w.words n) = 0
    omega
  have source : val32 u.mem B (src.offset n) (w.words n) = val32 s.mem B (src.offset n) (w.words n) :=
    Ou.val32 (by simp only [arr, S] at srcSep; omega) (by omega)
  refine WP.seq (WP.mono (copy_loc_ok hu w (.array w 0) src
    (by simp only [offset_array]; unfold S at f0; omega) srcBound sepSource)
    fun v ⟨hv, Ov, input, Kv⟩ => ?_)
  rw [offset_array] at Ov input
  change num v.mem B (w.words n) 0 = val32 u.mem B (src.offset n) (w.words n) at input
  have vKeep : Keep B (w.words n) [0] [] u.mem v.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ov) (by unfold S; omega) (by simp)
  have vFrame : Outside B hdr (4 * (15 * (w.words n + 2))) s.mem v.mem :=
    Ou.trans (Ov.mono (by unfold arr; omega)
      (by unfold arr S; omega))
  have modulus : val32 v.mem B (mo.offset n) (w.words n) = val32 s.mem B (mo.offset n) (w.words n) :=
    vFrame.val32 (by simp only [arr, S] at moSep; omega) (by omega)
  refine WP.mono (copy_loc_ok hv w (.array w aM) mo
    (by simp only [offset_array]; unfold S at fm; omega) moBound sepModulus)
    fun t ⟨ht, Ot, valueM, Kt⟩ => ?_
  rw [offset_array] at Ot valueM
  change num t.mem B (w.words n) aM = val32 v.mem B (mo.offset n) (w.words n) at valueM
  have tKeep : Keep B (w.words n) [aM] [] v.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ot) (by unfold S; omega) (by simp)
  have bankfit (j : Nat) (hj : j < 15) : arr (w.words n) j + S (w.words n) ≤ 2 ^ 64 := by
    have fit := H.ws.fit64 hj
    rwa [kw_words h.width] at fit
  refine ⟨ht, vFrame.trans (Ot.mono (by unfold arr; omega)
    (by unfold arr S aM; omega)), ?_, valueM.trans modulus, ?_,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · rw [tKeep.num (by decide) (by simp) (bankfit _ (by decide)), input, source]
  · intro j hj j0 jm
    rw [tKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm jm)
      (by simp) (bankfit j hj),
      vKeep.num (by simp only [List.mem_singleton]; intro k e; subst k; exact Ne.symm j0)
      (by simp) (bankfit j hj), zeros j hj]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
