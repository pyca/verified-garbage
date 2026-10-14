module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86

/-! # brainpoolP256r1 public keys on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_brainpoolp256r1_public_key`. -/
def publicKeyBrainpoolP256r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.brainpoolp256r1

end VG.Impl.EcKey.X86
