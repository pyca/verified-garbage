module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ClearTop
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Load the shared division bank at the public runtime width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num arr S)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs)

theorem divisionLoad_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {src divisor : Loc}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (L : DivisionInputs Z (w.words n) (src.offset n) (divisor.offset n)) :
    WP isa (divisionLoad w src divisor) s fun t =>
      Ws t B Z n N ∧ Outside B hdr (4 * (4 * (w.words n + 2))) s.mem t.mem ∧
      num t.mem B (w.words n) 0 = val32 s.mem B (src.offset n) (w.words n) ∧
      num t.mem B (w.words n) 2 = val32 s.mem B (divisor.offset n) (w.words n) ∧
      w32 t.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  have f0 := H.ws.arr_fit (j := 0) (by decide)
  have f2 := H.ws.arr_fit (j := 2) (by decide)
  rw [kw_words h.width] at f0 f2
  have srcBound := L.source_bound
  have divBound := L.divisor_bound
  have srcSep := L.source_outside
  have divSep := L.divisor_outside
  have sepSource : (Loc.array w 0).offset n + 4 * w.words n ≤ src.offset n ∨
      src.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n := by
    simp only [offset_array, arr, S] at *
    omega
  have sepDivisor : (Loc.array w 2).offset n + 4 * w.words n ≤ divisor.offset n ∨
      divisor.offset n + 4 * w.words n ≤ (Loc.array w 2).offset n := by
    simp only [offset_array, arr, S] at *
    omega
  unfold divisionLoad VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clearTop_ok h w (j := 2)
    (by rw [offset_array]; unfold S at f2; omega)) fun u ⟨hu, Ou, topU, Ku⟩ => ?_)
  rw [offset_array] at Ou topU
  have uFrame : Outside B hdr (4 * (4 * (w.words n + 2))) s.mem u.mem :=
    Ou.mono (by unfold arr; omega) (by unfold arr S; omega)
  have source : val32 u.mem B (src.offset n) (w.words n) =
      val32 s.mem B (src.offset n) (w.words n) :=
    uFrame.val32 (by simp only [arr, S] at srcSep; omega) (by omega)
  refine WP.seq (WP.mono (copy_loc_ok hu w (.array w 0) src
    (by rw [offset_array]; unfold S at f0; omega) srcBound sepSource)
    fun v ⟨hv, Ov, input, Kv⟩ => ?_)
  rw [offset_array] at Ov input
  change num v.mem B (w.words n) 0 = val32 u.mem B (src.offset n) (w.words n) at input
  have vFrame : Outside B hdr (4 * (4 * (w.words n + 2))) s.mem v.mem :=
    uFrame.trans (Ov.mono (by unfold arr; omega) (by unfold arr S; omega))
  have topV : w32 v.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 := by
    rw [Ov.w32 (by unfold arr S; omega) (by unfold S at f2; omega), topU]
  have modulus : val32 v.mem B (divisor.offset n) (w.words n) =
      val32 s.mem B (divisor.offset n) (w.words n) :=
    vFrame.val32 (by simp only [arr, S] at divSep; omega) (by omega)
  refine WP.mono (copy_loc_ok hv w (.array w 2) divisor
    (by rw [offset_array]; unfold S at f2; omega) divBound sepDivisor)
    fun t ⟨ht, Ot, valueD, Kt⟩ => ?_
  rw [offset_array] at Ot valueD
  change num t.mem B (w.words n) 2 = val32 v.mem B (divisor.offset n) (w.words n) at valueD
  have topT : w32 t.mem B (arr (w.words n) 2 + 4 * w.words n) = 0 := by
    rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by unfold S at f2; omega), topV]
  refine ⟨ht, vFrame.trans (Ot.mono (by unfold arr; omega) (by unfold arr S; omega)),
    ?_, valueD.trans modulus, topT, (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  change val32 t.mem B (arr (w.words n) 0) (w.words n) = _
  rw [Ot.val32 (by unfold arr S; omega) (by unfold S at f0; omega)]
  exact input.trans source

end VG.Proof.RsaKeyGen.X86.KeyRuntime
