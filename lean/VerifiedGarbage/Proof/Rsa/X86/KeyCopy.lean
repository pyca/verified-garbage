module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Copying a key-workspace array -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem copy_ok {s : State} {B : Addr} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) :
    WP isa (copy w o a) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Keeps [.eax, .ecx, .edx, .ebp] s t ∧
      w32 t.mem B (arr w o + 4 * w) = w32 s.mem B (arr w o + 4 * w) := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  simp only [S] at fo fa
  have sep : arr w o = arr w a ∨ arr w o + 4 * w ≤ arr w a ∨ arr w a + 4 * w ≤ arr w o := by
    by_cases e : o = a
    · exact .inl (congrArg (arr w) e)
    · have := arr_disj (w := w) e; unfold S at this; exact .inr (by omega)
  change WP isa (VG.Impl.Rsa.X86.Div.copyWords w (arr w a) (arr w o)) s _
  refine WP.mono (Div.copyWords_ok h.workspace h.wpos (by omega) (by omega) sep) ?_
  rintro t ⟨frame, value, rest⟩
  exact ⟨h.rest rest, Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp), value, rest, frame.w32 (by omega) (by have := h.workspace.nowrap; omega)⟩
end VG.Proof.Rsa.X86.Keys
