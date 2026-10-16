module

public import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
public import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Canonical modular doubling from the initialized workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem doubleCore_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (ready : CoreReady base size out tmp a b mod acc n s)
    (reduce : CsubCtx s base size out acc mod tmp n)
    (two : w32 s.mem (State.addr base) a = 2) :
    WP isa doubleCore s fun t =>
      val32 t.mem (State.addr base) out n =
        (2 * val32 s.mem (State.addr base) b n) % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have ctx := ready.round.ctx
  have count := ctx.count
  have nowrap := ctx.workspace.nowrap
  have mFits := ctx.mFits
  have sep := ctx.accM
  rw [doubleCore, WP.seq_iff]
  refine WP.mono (doubleProduct_ok s ready two) ?_
  rintro u ⟨value, finish, outside, rest⟩
  have modEq := outside.val32 (d := mod) (k := n) (by omega) (by omega)
  have ru : CsubCtx u base size out acc mod tmp n := {
    reduce with sub := { reduce.sub with writable := by rw [rest.wr]; exact reduce.sub.writable } }
  refine WP.mono (montFinish_ok u ru (by omega) ctx.tmpFits finish.ptr finish.count
    finish.outPtr finish.accPtr finish.mPtr ?_) ?_
  · rw [value, modEq]
    have := ready.round.operand
    omega
  · rintro t ⟨val, frame, keep⟩
    refine ⟨?_, ?_, rest.trans keep⟩
    · rw [val, value, modEq]
    · exact (Outs.of_outside outside (by simp)).trans (frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        exact Or.inr hr))

end VG.Proof.Bignum.Arm
