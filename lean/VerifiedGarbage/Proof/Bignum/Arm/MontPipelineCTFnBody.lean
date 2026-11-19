module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
meta import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! ### `Bignum.Arm.MontPipelineCTBody`, which only this module used -/

section

/-! ### `Bignum.Arm.MontPipelineCTCore`, which only this module used -/

section

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
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fits])
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

end

end

/-! Reuse the original public initialization for any scanning-round implementation. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem body_ct (round : Prog isa) (law : LoopLaw round) (ctLaw : LoopCTLaw round) {base : BitVec 32} {size out tmp a b mod acc n : Nat} (even : n % 2 = 0) (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => InitReady base size out tmp a b mod acc n s ∧
      InitReady base size out tmp a b mod acc n t) (VG.Impl.Bignum.Arm.MontPipeline.body round) (fun _ _ => True) := by
  let P := InitReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) montInit (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨is, rs, _⟩ := h.1.secret
    obtain ⟨it, rt, _⟩ := h.2.secret
    exact ⟨montInit_ct s t tr1 tr2 u v trivial trivial
      ⟨rs.tmpPtr.trans rt.tmpPtr.symm, rs.accPtr.trans rt.accPtr.symm, rs.count.trans rt.count.symm⟩ e1 e2, trivial⟩
  have wp (s : State) (h : P s) : WP isa montInit s (CoreReady base size out tmp a b mod acc n) := by
    obtain ⟨inv, regs, inverse⟩ := h.secret
    exact WP.mono (montInit_ok s h.ctx regs h.operand inverse) (fun _ h => h.1)
  exact (pair_posts ct wp).seq (core_ct round law ctLaw even ht)


end VG.Proof.Bignum.Arm.MontPipeline

end

end


/-! The callable arithmetic body retains the native public layout and index schedule. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem fnBody_ct (round : Prog isa) (law : LoopLaw round) (ctLaw : LoopCTLaw round) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      (VG.Impl.Bignum.Arm.MontPipeline.fnBody round) (fun _ _ => True) := by
  have ct : RelCT isa (fun s t => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t)
      (.block MontFn.bases) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.ptr.trans h.2.ptr.symm
    · exact h.1.outIndex.trans h.2.outIndex.symm
    · exact h.1.aIndex.trans h.2.aIndex.symm
    · exact h.1.bIndex.trans h.2.bIndex.symm
  exact (pair_posts ct (bases_ready ho ha hb)).seq (body_ct round law ctLaw (by omega_using []) fit)


end VG.Proof.Bignum.Arm.MontPipeline
