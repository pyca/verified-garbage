module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout

/-! The secp256k1 comb reuses the ladder's accumulator and addition temporary. -/

@[expose] public section
namespace VG.Proof.Secp256k1.Arm
open VG VG.Impl.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout (u : Bool := false) : Layout (secp256k1CombWith u) := by
  refine ⟨by decide +revert,by decide +revert,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide +revert,by decide +revert⟩
  all_goals decide +kernel +revert

end VG.Proof.Secp256k1.Arm
