module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-! # P-256 public keys on x86-64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p256

/-- `vg_ec_p256_public_key_adx`. -/
def publicKeyP256Adx : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p256x

end VG.Impl.EcKey.X86_64

namespace VG.Impl.EcKey.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ec_p256_public_key` as emitted: its code, then its cleanup. -/
def publicKeyP256 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP256

/-- `vg_ec_p256_public_key_adx` as emitted: its code, then its cleanup. -/
def publicKeyP256Adx : Prog isa := scrubAll .avx 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP256Adx

end VG.Impl.EcKey.X86_64.Fn
