module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionStore
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

/-! # The shared division bank exports quotient and remainder through one copy loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num arr S)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionOutputs)

theorem divisionStore_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width} {quotient remainder : Loc}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (L : DivisionOutputs Z (w.words n) (quotient.offset n) (remainder.offset n)) :
    WP isa (divisionStore w quotient remainder) s fun t =>
      Ws t B Z n N ∧ Outs B [(quotient.offset n, 4 * w.words n),
        (remainder.offset n, 4 * w.words n)] s.mem t.mem ∧
      val32 t.mem B (quotient.offset n) (w.words n) = num s.mem B (w.words n) 0 ∧
      val32 t.mem B (remainder.offset n) (w.words n) = num s.mem B (w.words n) 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have H := shrinkRt (h.runtime hw) bound
  have hn := h.old.workspace.nowrap
  have f0 := H.ws.arr_fit (j := 0) (by decide)
  have f1 := H.ws.arr_fit (j := 1) (by decide)
  rw [kw_words h.width] at f0 f1
  have qBound := L.quotient_bound
  have rBound := L.remainder_bound
  have qSep := L.quotient_outside
  have rSep := L.remainder_outside
  have sep := L.separate
  have sepQ : quotient.offset n + 4 * w.words n ≤ (Loc.array w 0).offset n ∨
      (Loc.array w 0).offset n + 4 * w.words n ≤ quotient.offset n := by
    simp only [offset_array, arr, S] at *
    omega
  have sepR : remainder.offset n + 4 * w.words n ≤ (Loc.array w 1).offset n ∨
      (Loc.array w 1).offset n + 4 * w.words n ≤ remainder.offset n := by
    simp only [offset_array, arr, S] at *
    omega
  unfold divisionStore
  refine WP.seq (WP.mono (copy_loc_ok h w quotient (.array w 0) qBound
    (by rw [offset_array]; unfold S at f0; omega) sepQ) fun u ⟨hu, Ou, Q, Ku⟩ => ?_)
  rw [offset_array] at Q
  have R : val32 u.mem B (Loc.array w 1 |>.offset n) (w.words n) = num s.mem B (w.words n) 1 := by
    rw [offset_array]
    exact Ou.val32 (by simp only [arr, S] at qSep; unfold arr S; omega)
      (by unfold S at f1; omega)
  refine WP.mono (copy_loc_ok hu w remainder (.array w 1) rBound
    (by rw [offset_array]; unfold S at f1; omega) sepR) fun t ⟨ht, Ot, V, Kt⟩ => ?_
  refine ⟨ht, (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp)),
    ?_, V.trans R, Ku.trans Kt⟩
  rw [Ot.val32 sep (by omega)]
  exact Q

end VG.Proof.RsaKeyGen.X86.KeyRuntime
