module

public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2

/-! # Normalized modulus preparation through shared Montgomery calls -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.NormalizedPrecompute
open VG VG.Arm

def precompute (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq importModulus (.seq precomputeInverse (NormalizedR2.r2 op))

end VG.Impl.Bignum.Arm.NormalizedPrecompute
