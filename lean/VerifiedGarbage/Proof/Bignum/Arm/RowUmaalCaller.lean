module

public import VerifiedGarbage.Proof.Bignum.Arm.RowCaller
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

/-! UMAAL arithmetic inherited by callers of the shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG.Impl.Bignum.Arm

def umaalCaller : VG.Arm.CallerTransform := rowCaller rowU row_sim rfl rfl

end VG.Proof.Bignum.Arm
