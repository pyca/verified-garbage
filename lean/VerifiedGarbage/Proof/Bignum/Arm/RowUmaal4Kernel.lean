module

public import VerifiedGarbage.Proof.Bignum.Arm.RowKernel
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Main
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4CT
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
public import VerifiedGarbage.Proof.Bignum.Arm.RowState

/-! Four-word UMAAL implements the common row interface. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def RowKernel.umaal4 : RowKernel where
  code := rowU4
  correct := by
    intro s base size o b n ctx hn hp0 hp12 hc
    exact row4_ok s ctx hn hp0 hp12 hc
  ct := row4_ct
  fullCT := row4Full_ct
  stackZero := rfl
  callsNil := rfl

end VG.Proof.Bignum.Arm
