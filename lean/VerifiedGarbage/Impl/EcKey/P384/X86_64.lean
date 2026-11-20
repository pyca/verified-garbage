module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-! # P-384 public keys on x86-64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p384

/-- `vg_ec_p384_public_key_adx`. -/
def publicKeyP384Adx : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p384x

end VG.Impl.EcKey.X86_64

namespace VG.Impl.EcKey.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ec_p384_public_key` as emitted: its code, then its cleanup. -/
def publicKeyP384 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP384

/-- `vg_ec_p384_public_key_adx` as emitted: its code, then its cleanup. -/
def publicKeyP384Adx : Prog isa := scrubAll .avx 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP384Adx

end VG.Impl.EcKey.X86_64.Fn
