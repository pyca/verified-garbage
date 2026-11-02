module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
meta import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
meta import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

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
  exact (pair_posts ct (bases_ready ho ha hb)).seq (body_ct round law ctLaw (by omega) fit)


end VG.Proof.Bignum.Arm.MontPipeline
