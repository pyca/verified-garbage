module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Constant-address array selection in the RSA key workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem sel_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hs : sl + 4 ≤ hdr)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel w o a b sl) s fun t =>
      Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have head := h.hdr_le
  have sep (j : Nat) : o = j ∨ arr w o + 4 * w ≤ arr w j ∨ arr w j + 4 * w ≤ arr w o := by
    by_cases eq : o = j
    · exact .inl eq
    · have := arr_disj (w := w) eq; unfold S at this; exact .inr (by omega)
  unfold sel
  change WP isa (.seq _ (VG.Impl.Mont.X86.Dynamic.selectsW w (arr w a) (arr w b) (arr w o))) s _
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have hu := h.workspace.of_keeps U.keeps (by decide)
  refine wp_subS (readSrc_sc hu (by omega)) fun v V _ => WP.block_nil ?_
  have mem : v.mem = s.mem := V.mem.trans U.mem
  have mask : v.gpr .ecx = if decide (slot s.mem B sl ≠ 0) then BitVec.allOnes 32 else 0 := by
    rw [V.gpr, U.gpr, U.mem]
    have word : s.mem.readW (off B sl) 32 = BitVec.ofNat 32 (slot s.mem B sl) := by
      simp [slot, w32]
    rw [word]
    have cases : slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 := by omega
    rcases cases with e | e <;> rw [e] <;> rfl
  have hv := hu.of_keeps V.keeps (by decide)
  simp only [S] at fo fa fb
  refine WP.mono (selectsW_ok hv _ mask h.wpos (by omega) (by omega) (by omega) ?_ ?_) ?_
  · rcases sep a with e | e; exact .inl (congrArg (arr w) e); exact .inr e
  · rcases sep b with e | e; exact .inl (congrArg (arr w) e); exact .inr e
  rintro t ⟨frame, value, rest⟩
  have r : Keeps [.eax, .ecx, .edx, .ebp] s t :=
    ((U.keeps.trans V.keeps).mono (by decide)).trans (rest.mono (by decide))
  refine ⟨h.rest r, ?_, ?_, r⟩
  · rw [mem] at frame
    exact Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  · change val32 t.mem B (arr w o) w = _
    rw [value, mem]
    by_cases e : slot s.mem B sl = 0 <;> simp [e, num]
end VG.Proof.Rsa.X86.Keys
