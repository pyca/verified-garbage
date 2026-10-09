import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ball
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Impl.MlDsa.AArch64.Optimized.Ball

/-- The SHA3 permutation used by the registered resident backend. -/
def sha3Callee : Impl.Sha3.AArch64.Callee where
  name := "vg_keccak_f1600_sha3"
  code := Impl.Sha3.AArch64.Sha3.Vector.permute
  suffix := "_sha3"
  pairedSha3 := true

/-- Match the registered SHA3 streaming entry points, including resident absorb. -/
def residentCallee : Impl.Sha3.AArch64.Callee :=
  { sha3Callee with absorbOverride := some (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb sha3Callee) }

/-- SHA3-capable sampling uses the verified lazy parser; other backends retain
 their original sampler and call graph. -/
def selected (c : Impl.Sha3.AArch64.Callee) : Prog VG.AArch64.isa :=
  if c.pairedSha3 then codeWith residentCallee else Sample.sampleInBallWith c
end VG.Impl.MlDsa.AArch64.Optimized.Ball
