module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! Canonical subtraction composes with every verified constant-time scanning loop. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem rounds_finishReady (round : Prog isa) (law : LoopLaw round) {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (even : n % 2 = 0) (s : State) (h : CoreReady base size out tmp a b mod acc n s) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.rounds round) s (FinishReady base size tmp out acc mod n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.round.secret
  refine WP.mono (law s h.round.ctx even hdr h.round.ptr h.zero h.round.operand inverse) ?_
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

theorem core_ct (round : Prog isa) (law : LoopLaw round) (ctLaw : LoopCTLaw round) {base : BitVec 32} {size out tmp a b mod acc n : Nat} (even : n % 2 = 0) (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => CoreReady base size out tmp a b mod acc n s ∧
      CoreReady base size out tmp a b mod acc n t) (VG.Impl.Bignum.Arm.MontPipeline.core round) (fun _ _ => True) := by
  have rounds := pair_posts (P := CoreReady base size out tmp a b mod acc n)
    ((ctLaw even).mono (fun _ _ h => ⟨h.1.round, h.2.round⟩) (fun _ _ h => h)) (rounds_finishReady round law even)
  exact rounds.seq (montFinish_ct ht)


end VG.Proof.Bignum.Arm.MontPipeline
