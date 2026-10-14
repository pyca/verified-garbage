module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86

/-! # brainpoolP512r1 public keys on x86 (32-bit): eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_brainpoolp512r1_public_key`. -/
def publicKeyBrainpoolP512r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.brainpoolp512r1

end VG.Impl.EcKey.X86
