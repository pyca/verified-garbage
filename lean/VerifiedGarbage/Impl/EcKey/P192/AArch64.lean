module

public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64

@[expose] public section

namespace VG.Impl.EcKey.AArch64

/-- p192 public-key derivation by the complete ladder. -/
def publicKeyP192 : Prog VG.AArch64.isa :=
  Cfg.publicKeyWith Ecdsa.AArch64.p192 Ecdsa.AArch64.P192.gMul

end VG.Impl.EcKey.AArch64
