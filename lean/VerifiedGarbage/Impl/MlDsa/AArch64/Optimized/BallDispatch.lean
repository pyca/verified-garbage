module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ball
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.Ball

/-- SHA3-capable sampling uses the verified lazy parser; other backends retain
 their original sampler and call graph. -/
def selected (c : Impl.Sha3.AArch64.Callee) : Prog VG.AArch64.isa :=
  if c.pairedSha3 then codeWith Impl.Sha3.AArch64.Sha3.Vector.callee else Sample.sampleInBallWith c
end VG.Impl.MlDsa.AArch64.Optimized.Ball
