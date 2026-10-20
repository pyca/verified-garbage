module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTRoundPrepare
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! End-to-end timing for the named shared compact-window primality call. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem roundKernel_ct (v : RoundImpl) : RelCT isa (Two RoundKernelStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) (fun _ _ => True) :=
  RelCT.assoc (roundPrepared_ct.seq ((sharedRoundCall_ct v).seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
