module

public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Step
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Value
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! A step of the two-row scan extends the invariant by a word. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem step_inv {s0 s : State} {a0 q0 a1 q1 base : BitVec 32} {size acc b mod n j p : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (inv : Inv s0 a0 q0 a1 q1 base acc b mod n j p s)
    (hj : j + 3 ≤ n) (hp : j ≤ p + 1) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.step (4 * (j - p))) s fun t =>
      Inv s0 a0 q0 a1 q1 base acc b mod n (j + 1) p t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have lag := inv.lag
  have ws := ctx.workspace.congr inv.rest.wr
  refine WP.mono (step_ok s ws (k := 4 * (j - p)) (by omega) (by omega) (by omega) (by omega)
    inv.outPtr inv.bPtr inv.mPtr) ?_
  rintro t ⟨value, mem, rest⟩
  have e (x : Nat) : x + 4 * p + 4 * (j - p) = x + 4 * j := by omega
  rw [e, e, e, inv.scalar0, inv.quotient0, inv.scalar1, inv.quotient1] at value
  rw [e] at mem
  have oldT := inv.outside.w32 (d := acc + 4 * j + 8) (by omega) (by omega)
  have oldB2 := inv.outside.w32 (d := b + 4 * j + 8) (by rcases ctx.accB with h | h <;> omega) (by omega)
  have oldM2 := inv.outside.w32 (d := mod + 4 * j + 8) (by rcases ctx.accM with h | h <;> omega) (by omega)
  have oldB1 := inv.outside.w32 (d := b + 4 * j + 4) (by rcases ctx.accB with h | h <;> omega) (by omega)
  have oldM1 := inv.outside.w32 (d := mod + 4 * j + 4) (by rcases ctx.accM with h | h <;> omega) (by omega)
  rw [oldT, oldB2, oldM2, oldB1, oldM1] at value
  have writes := writeW32_outside s.mem (State.addr base) (d := acc + 4 * j) (t.gpr .r6) (by omega)
  rw [← mem] at writes
  have low := writes.val32 (d := acc) (k := j) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (acc + 4 * j) = (t.gpr .r6).toNat := by
    rw [mem, w32_write_self]
  have stored : val32 t.mem (State.addr base) acc (j + 1) =
      val32 s.mem (State.addr base) acc j + 2 ^ (32 * j) * (t.gpr .r6).toNat := by
    rw [val32_succ, low, top]
  have keep (r : Reg) (h : r ∉ [.r3, .r5, .r6, .r7, .r8, .r11]) : t.gpr r = s.gpr r := rest.gpr r h
  refine ⟨by omega, by omega, (keep .r0 (by decide)).trans inv.outPtr,
    (keep .r12 (by decide)).trans inv.bPtr, (keep .r4 (by decide)).trans inv.mPtr,
    (keep .lr (by decide)).trans inv.count, (keep .r1 (by decide)).trans inv.scalar0,
    (keep .r2 (by decide)).trans inv.quotient0, (keep .r9 (by decide)).trans inv.scalar1,
    (keep .r10 (by decide)).trans inv.quotient1,
    (inv.outside.mono (Nat.le_refl _) (by omega)).trans (writes.mono (by omega) (by omega)), ?_,
    inv.rest.trans (rest.mono (by decide))⟩
  refine value_extend inv.value ?_ stored
  rw [show acc + 4 * (j + 2) = acc + 4 * j + 8 by omega, show b + 4 * (j + 2) = b + 4 * j + 8 by omega,
    show mod + 4 * (j + 2) = mod + 4 * j + 8 by omega, show b + 4 * (j + 1) = b + 4 * j + 4 by omega,
    show mod + 4 * (j + 1) = mod + 4 * j + 4 by omega]
  exact value

end VG.Proof.Bignum.Arm.Fios2
