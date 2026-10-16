module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86

/-! # brainpoolP384r1 public keys on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_brainpoolp384r1_public_key`. -/
def publicKeyBrainpoolP384r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.brainpoolp384r1

end VG.Impl.EcKey.X86
