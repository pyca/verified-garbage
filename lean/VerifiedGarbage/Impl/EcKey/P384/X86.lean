module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P384.X86Comb

/-! # P-384 public keys on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.p384Comb

end VG.Impl.EcKey.X86
