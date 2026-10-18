module

public import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps

/-! # A power-of-two modulus for the exact product of the key exponents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem setTop_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) : WP isa (.block (setTop w j)) s fun t =>
      Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = val32 s.mem B (arr w j) (w - 1) + 2 ^ (32 * (w - 1)) * 2 ^ 31 ∧
      Keeps [.eax] s t := by
  have fit := h.arr_fit hj
  have nowrap := h.workspace.nowrap
  have pos := h.wpos
  simp only [S] at fit
  unfold setTop
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.rest U.keeps (by decide) (by decide)
  refine wp_storeS (hu.workspace.ea (d := arr w j + 4 * (w - 1)) (by omega))
    (hu.workspace.write (by omega)) fun t T => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off B (arr w j + 4 * (w - 1))) (0x80000000 : BitVec 32) := by
    rw [T.mem, U.gpr, U.mem]
  have frame := writeW32_outside s.mem B (d := arr w j + 4 * (w - 1))
    (0x80000000 : BitVec 32) (by omega)
  rw [← mem] at frame
  refine ⟨hu.rest (T.keeps []), Keep.of_arr frame (by simp only [S]; omega) (by simp), ?_,
    U.keeps.trans ((T.keeps []).mono (by decide))⟩
  change val32 _ _ _ _ = _
  have expand := val32_succ t.mem B (arr w j) (w - 1)
  rw [show w - 1 + 1 = w by omega] at expand
  rw [expand, frame.val32 (.inl (by omega)) (by omega)]
  congr 2
  simp only [w32]
  rw [mem, Mem.readW_writeW_self32]
  rfl

end VG.Proof.Rsa.X86.Recover
