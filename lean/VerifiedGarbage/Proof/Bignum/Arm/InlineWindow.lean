module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineOp
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds

/-! A scanning round supplies the existing window proof without a second CRT implementation. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.InlineWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

variable (round : Prog isa) (law : MontPipeline.LoopLaw round)

def arithmetic (base : BitVec 32) (len w : Nat) :
    TwoExp.Montgomery base len w (fun _ => True) [⟨State.addr base, 8 * len⟩] where
  op := MontPipeline.op round
  workspace := by simp
  stable := by intros; trivial
  op_ok := by
    intro s o a b ready _ ho ha hb ho0 operand
    refine WP.mono (montPipelineOp_ok round law s ready ho ha hb ho0 operand) ?_
    rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
    exact ⟨ready, modulus, bound, value, keeps, trivial, frame, rest⟩

theorem timing (ctLaw : MontPipeline.LoopCTLaw round) {base : BitVec 32} {len w : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    TwoExp.MontgomeryTiming (arithmetic round law base len w) where
  op_ct := by
    intro o a b ho ha hb
    exact (montPipelineOp_ct round law ctLaw ho ha hb fit).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.2⟩, ⟨h.2.1.1, h.2.1.2.2⟩, h.2.2⟩)
      (fun _ _ _ => trivial)

def kernel (ctLaw : MontPipeline.LoopCTLaw round) : WindowKernel where
  code := SharedWindow.phase (MontPipeline.op round)
  correct := by
    intro s base ep len w M x eb h fits
    refine WP.mono (sharedWindowExpPhase_ok (arithmetic round law base len w) s h trivial fits ?_) ?_
    · intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact h.separate
    · rintro t ⟨ready, value, modulus, r2, one, _, frame, rest⟩
      exact ⟨ready, value, modulus, r2, one, frame, rest⟩
  ct := by
    intro base ep len w M1 M2 x1 x2 eb1 eb2 fit fits positive length
    intro s t tr1 tr2 u v h e1 e2
    exact SharedWindow.phase_ct (arithmetic round law base len w) (timing round law ctLaw fit)
      fits positive length (by
        intro r hr
        have eq := List.mem_singleton.mp hr
        subst r
        exact h.1.separate) s t tr1 tr2 u v
      ⟨⟨h.1, trivial⟩, ⟨h.2.1, trivial⟩, h.2.2⟩ e1 e2

end VG.Proof.Bignum.Arm.InlineWindow
