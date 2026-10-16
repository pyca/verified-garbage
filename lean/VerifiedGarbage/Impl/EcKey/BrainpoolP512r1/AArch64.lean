module

public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64

@[expose] public section

namespace VG.Impl.EcKey.AArch64

/-- brainpoolp512r1 public-key derivation by the complete ladder. -/
def publicKeyBrainpoolP512r1 : Prog VG.AArch64.isa :=
  Cfg.publicKeyWith Ecdsa.AArch64.brainpoolp512r1 Ecdsa.AArch64.BrainpoolP512r1.gMul

end VG.Impl.EcKey.AArch64
