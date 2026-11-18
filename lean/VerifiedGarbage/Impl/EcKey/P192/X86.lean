module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P192.X86Comb

/-! # P-192 public keys on x86 (32-bit): three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p192_public_key`. -/
def publicKeyP192 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.p192Comb

end VG.Impl.EcKey.X86
