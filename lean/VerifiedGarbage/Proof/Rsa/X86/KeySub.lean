module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Native-word subtraction in the RSA key workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem sub3_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 w o a b) s fun t =>
      Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b =
        num s.mem B w a + 2 ^ (32 * w) * (t.gpr .ebx).toNat ∧
      (t.gpr .ebx).toNat ≤ 1 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have sa := arr_disj (w := w) hoa
  have sb := arr_disj (w := w) hob
  unfold sub3
  change WP isa (.seq (VG.Impl.Mont.X86.Dynamic.chainW .sbb w (arr w o) (arr w a) (arr w b)) _) s _
  simp only [S] at fo fa fb sa sb
  refine WP.seq (WP.mono (chainSubW_ok h.workspace h.wpos
    (by exact Nat.le_trans (by omega) fo) (by exact Nat.le_trans (by omega) fa)
    (by exact Nat.le_trans (by omega) fb) (by exact sa.imp (by omega) (by omega))
    (by exact sb.imp (by omega) (by omega))) ?_)
  rintro u ⟨frame, ⟨c, carry, value⟩, rest⟩
  refine wp_movS rfl fun v V _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have r : Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t :=
    (rest.mono (by decide)).trans ((V.keeps.trans T.keeps).mono (by decide))
  have mem : t.mem = u.mem := T.mem.trans V.mem
  have bit : (t.gpr .ebx).toNat = c.toNat := by
    rw [T.gpr, V.gpr, carry, ite_eq_left rfl]
    cases c <;> rfl
  refine ⟨h.rest r, ?_, ?_, ?_, r⟩
  · rw [mem]
    exact Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  · rw [num, mem, bit]; exact value
  · rw [bit]; cases c <;> decide
end VG.Proof.Rsa.X86.Keys
