module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
/-! # Load the shared division bank at the public runtime width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ClearTop.lean`, which only this module imported.
section

/-! # The division bank's extra divisor word is explicitly zero -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem clearTop_ok {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N)
    (w : Width) (fit : Loc.offset n (.array w j) + 4 * w.words n + 4 ≤ Z) :
    WP isa (clearTop w j) s fun t => Ws t B Z n N ∧
      Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem ∧
      w32 t.mem B (Loc.offset n (.array w j) + 4 * w.words n) = 0 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold clearTop
  simp only [List.append_assoc]
  refine h.ptr_ok (.array w j) (by decide) (by decide) (by omega) fun a K1 m1 P1 => ?_
  have ha := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine ha.bytes_ok w .edx fun b K2 m2 count => ?_
  refine wp_addS rfl fun c C _ => wp_movS rfl fun d U _ => ?_
  have K : Keeps [.eax, .edx, .ebp] s d :=
    ((K1.mono (by decide)).trans (K2.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (U.keeps.mono (by decide)))
  have hw := h.full.rt.of_keeps K
  have P2 : PtrAt b B .ebp (Loc.offset n (.array w j)) := by
    rw [PtrAt, K2.1 _ (by decide)]; exact P1
  have P : PtrAt d B .ebp (Loc.offset n (.array w j) + 4 * w.words n) := by
    rw [PtrAt, U.other _ (by decide), C.gpr, VG.Proof.Mont.X86.Rt.ptr_add P2, count]
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hw P (d := 0) (by omega))
    (VG.Proof.Mont.X86.Rt.ws_write hw (y := Loc.offset n (.array w j) + 4 * w.words n + 0)
      (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have memory : t.mem = s.mem.writeW (off B (Loc.offset n (.array w j) + 4 * w.words n)) (0#32) := by
    rw [T.mem, U.mem, C.mem, m2, m1, U.gpr, Nat.add_zero]
    rfl
  have O : Outside B (Loc.offset n (.array w j) + 4 * w.words n) 4 s.mem t.mem := by
    rw [memory]; exact writeW32_outside _ _ _ (by omega)
  have allK := K.trans (T.keeps _)
  refine ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega)), O, ?_, allK⟩
  rw [memory, w32_write_self]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

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
