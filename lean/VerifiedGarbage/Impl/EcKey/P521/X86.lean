module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P521.X86Comb

/-! # P-521 public keys on x86 (32-bit): nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.p521Comb

end VG.Impl.EcKey.X86
