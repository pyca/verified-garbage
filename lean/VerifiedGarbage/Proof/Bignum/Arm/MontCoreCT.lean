module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.MontRoundsCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontFinishCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Constant time of canonical Montgomery multiplication after initialization -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure CoreReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop where
  round : RoundReady base size tmp a b mod acc n 0 s
  outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out
  zero : val32 s.mem (State.addr base) acc (n + 2) = 0

theorem montRounds_finishReady {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (s : State) (h : CoreReady base size out tmp a b mod acc n s) :
    WP isa montRounds s (FinishReady base size tmp out acc mod n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.round.secret
  refine WP.mono (montRounds_ok s h.round.ctx hdr h.round.ptr h.zero h.round.operand inverse) ?_
  intro t loop
  have nowrap := h.round.ctx.workspace.nowrap
  have layout := h.round.ctx.layout
  have fits := h.round.ctx.tmpFits
  have oldOut := outs_word32 loop.outside (d := tmp + 24) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine ⟨h.round.ctx.workspace.congr loop.rest.wr, loop.ptr, loop.hdr.count, ?_,
    loop.hdr.accPtr, loop.hdr.mPtr⟩
  apply BitVec.eq_of_toNat_eq
  exact oldOut.trans (congrArg BitVec.toNat h.outPtr)

theorem montCore_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat} (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => CoreReady base size out tmp a b mod acc n s ∧
      CoreReady base size out tmp a b mod acc n t) montCore (fun _ _ => True) := by
  have rounds := pair_posts (P := CoreReady base size out tmp a b mod acc n)
    (montRounds_ct.mono (fun _ _ h => ⟨h.1.round, h.2.round⟩) (fun _ _ h => h)) montRounds_finishReady
  exact rounds.seq (montFinish_ct ht)

end VG.Proof.Bignum.Arm
