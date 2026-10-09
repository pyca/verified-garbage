import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG.AArch64

/-- The selected forward transform's positive normalization. `q` contains the
modulus in each word; `tmp` is distinct from both input and modulus. -/
def positive (d tmp q : VReg) : List Instr :=
  [.vop (.shift .sshr .s4 tmp d 23), .vop (.mls d tmp q), .vop (.add .s4 d d q)]

/-- Ordinary-form twiddle multiplication using its exact reciprocal. -/
def fastMul (d tmp z recip q : VReg) : List Instr :=
  [.vop (.sqdmulh tmp d recip), .vop (.mul d d z), .vop (.mls d tmp q)]

end VG.Impl.MlDsa.AArch64.Optimized
