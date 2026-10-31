module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ops -- shake: keep (retains the exported PMULL value interface)
public import VerifiedGarbage.Proof.Gcm.Clmul.Arith -- shake: keep (exports the shared arithmetic under its existing names)

/-! # Shared carryless arithmetic for AArch64 GHASH -/

@[expose] public section
namespace VG.Proof.Gcm.AArch64.Pmull

export VG.Proof.Gcm.Clmul (gp_shl clSteps gp_clSteps gp_lsb gp_polyMul polyMul_comm ψ φ_polyMul ψ_xor φ_append φ_v ρ ρ_xor φ_ext8 ρ_ext8_self ψ_poly φ_ext8_self ρ_add_polyMul φ_fold ρ_reduce gp_xInv2 x2_φ_xInv2 gp_shl1 gp_ushr63 ψ_ushr63 ψ_shl1 gp_one64 ushr63 ρ_polyMul_bit twist_ρ twistV_ρ)

namespace Prod
export VG.Proof.Gcm.Clmul.Prod (val val_zero val_acc)
end Prod

end VG.Proof.Gcm.AArch64.Pmull
