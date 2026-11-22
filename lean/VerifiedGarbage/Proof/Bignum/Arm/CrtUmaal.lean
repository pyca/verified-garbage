module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFios
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineBase
import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
import VerifiedGarbage.Proof.Bignum.Arm.FiosCT
import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Bignum.Arm.FiosCode
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.Arm.InlineWindow`, which only this module used -/

section

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
    intro s base ep len w M x eb h fits _ _
    refine WP.mono (sharedWindowExpPhase_ok (arithmetic round law base len w) s h trivial fits ?_) ?_
    · intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact h.separate
    · rintro t ⟨ready, value, modulus, r2, one, _, frame, rest⟩
      exact ⟨ready, value, modulus, r2, one, frame.mono (by simp), rest⟩
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

end

end

/-! # `vg_rsa_private_crt_umaal`: the private-key operation with `umaal` rows -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosRound.lean`, which only this module imported.
section

/-! The integrated scan meets the unchanged complete Montgomery round contract. -/

section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem round_law : MontPipeline.RoundLaw VG.Impl.Bignum.Arm.Fios.round := by
  intro s base size tmp a b mod acc n i inv ctx even hdr hi ptr hT hB hInv
  have count := ctx.count
  rw [VG.Impl.Bignum.Arm.Fios.round,WP.seq_iff]
  refine WP.mono (args_ok s ctx hdr hi ptr) ?_
  rintro u ⟨scalar,p0,p12,p4,p2,cnt,carryA,carryM,memU,restU⟩
  let c : Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr restU.wr,ctx.accFits,ctx.bFits,ctx.mFits,ctx.accB,ctx.accM⟩
  rw [WP.seq_iff]
  refine WP.mono (code_ok u c (by omega) even p0 p12 p4 cnt carryA carryM ?_ ?_) ?_
  · simpa only [memU,p2] using hInv
  · intro q hq
    rw [memU,scalar]
    exact round_fit hT (s.mem.readW (off (State.addr base) (a+4*i)) 32).isLt
      hB hq (val32_lt s.mem (State.addr base) mod n)
  · rintro v ⟨quotient,ptrV,outsideV,keepV⟩
    rw [memU,scalar] at quotient
    rw [memU] at outsideV
    exact finishRound_ok s v ctx hdr hi hT hB quotient ptrV outsideV
      ((restU.mono (by decide)).trans keepV)

end VG.Proof.Bignum.Arm.Fios
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Arm VG.Impl.Bignum.Arm

theorem crtUmaal_verified :
    Verified target CrtFios.code (Proof.Rsa.privateCrtContract abi 104) :=
  umaalArithmetic_verified (crt_verified (kernel := InlineWindow.kernel Fios.round (MontPipeline.RoundLaw.loop Fios.round_law)
    (MontPipeline.RoundCTLaw.loop Fios.round_law (by
      intro base size tmp a b mod acc n i _ hi
      exact Fios.round_ct hi))))

theorem crtUmaal_verifiedP :
    Verified target CrtFios.codeGiven (Proof.Rsa.privateCrtPrecomputedContract abi 104) :=
  umaalArithmetic_verified (crt_verifiedP (kernel := InlineWindow.kernel Fios.round (MontPipeline.RoundLaw.loop Fios.round_law)
    (MontPipeline.RoundCTLaw.loop Fios.round_law (by
      intro base size tmp a b mod acc n i _ hi
      exact Fios.round_ct hi))))

end VG.Proof.Bignum.Arm
