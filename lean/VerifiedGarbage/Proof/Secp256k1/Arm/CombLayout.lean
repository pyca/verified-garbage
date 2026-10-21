module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout

/-! The secp256k1 comb reuses the ladder's accumulator and addition temporary. -/

@[expose] public section
namespace VG.Proof.Secp256k1.Arm
open VG VG.Impl.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout : Layout secp256k1Comb := by
  refine ⟨by decide,by decide,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide,by decide⟩
  all_goals decide +kernel

end VG.Proof.Secp256k1.Arm
