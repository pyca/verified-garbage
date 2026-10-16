module

public import VerifiedGarbage.Impl.Bignum.Arm.ImportArray
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut

/-! # Load the shared public-key precomputation without recomputing R²

The initialized workspace is in r0, the packed precomputation in r4.
The first array is the modulus, the second R²; both contain w 64-bit words.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def pdImport : Prog isa := .seq (.block [.mov .r2 (.imm 0)])
  (.seq importArray (.seq (.block precomputeOutAdvance) importArray))

end VG.Impl.Bignum.Arm
