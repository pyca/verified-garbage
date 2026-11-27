module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-! # P-224 public keys on x86-64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p224

end VG.Impl.EcKey.X86_64

namespace VG.Impl.EcKey.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ec_p224_public_key` as emitted: its code, then its cleanup. -/
def publicKeyP224 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP224

end VG.Impl.EcKey.X86_64.Fn
