module

public import VerifiedGarbage.Proof.Rsa.X86.KeySelect
public import VerifiedGarbage.Proof.Mont.X86.ShiftDown

/-! # Halving an RSA workspace array with an incoming carry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem half_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (half w j) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat) / 2 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have fit := h.arr_fit hj
  simp only [S] at fit
  have nw := h.workspace.nowrap
  unfold half
  have wpos := h.wpos
  change WP isa (.seq (.block [.store (VG.Impl.Mont.X86.sc (arr w j + 4 * w)) .ebx])
    (VG.Impl.Mont.X86.Dynamic.shiftDown (w + 1) (arr w j))) s _
  refine WP.seq (wp_storeS (h.workspace.ea (by omega)) (h.workspace.write (by omega)) fun u U => WP.block_nil ?_)
  have hu := h.workspace.of_keeps (U.keeps []) (by decide)
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.shiftDown_ok hu (k := w + 1) (out := arr w j) (by omega) (by omega)) ?_
  rintro t ⟨frame, value, rest⟩
  have stored := writeW32_outside s.mem B (d := arr w j + 4 * w) (s.gpr .ebx) (by omega)
  have keepU : Keep B w [j] [] s.mem u.mem := by
    rw [U.mem]
    exact Keep.of_arr stored (by unfold S; omega) (by simp)
  have keepT : Keep B w [j] [] u.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  refine ⟨h.rest ((U.keeps _).trans rest), keepU.trans keepT, ?_, (U.keeps _).trans rest⟩
  have original : val32 u.mem B (arr w j) (w + 1) =
      num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat := by
    rw [val32_succ, U.mem, w32_write_self, stored.val32 (by omega) (by omega)]
  rw [original] at value
  have bound := val32_lt s.mem B (arr w j) w
  have positive : 0 < 2 ^ (32 * w) := Nat.two_pow_pos _
  have small : (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat) / 2 < 2 ^ (32 * w) := by
    have mul : 2 ^ (32 * w) * (s.gpr .ebx).toNat ≤ 2 ^ (32 * w) := by
      simpa using Nat.mul_le_mul_left (2 ^ (32 * w)) bit
    unfold num
    omega
  have lower := val32_lt t.mem B (arr w j) w
  rw [val32_succ] at value
  have topZero : w32 t.mem B (arr w j + 4 * w) = 0 := by
    by_contra ne
    have ge := Nat.mul_le_mul_left (2 ^ (32 * w)) (show 1 ≤ w32 t.mem B (arr w j + 4 * w) by omega)
    simp only [Nat.mul_one] at ge
    omega
  rw [topZero, Nat.mul_zero, Nat.add_zero] at value
  exact value
end VG.Proof.Rsa.X86.Keys
