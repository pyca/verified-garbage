module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Bignum.Arm.FiosCode
import VerifiedGarbage.Proof.Bignum.Arm.FiosRoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The integrated scan meets the unchanged complete Montgomery round contract. -/

@[expose] public section
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
      ((restU.mono (by simp [roundClobbers])).trans keepV)

end VG.Proof.Bignum.Arm.Fios
