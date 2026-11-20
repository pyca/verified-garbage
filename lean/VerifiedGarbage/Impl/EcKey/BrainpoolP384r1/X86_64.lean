module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64

/-! # brainpoolP384r1 on x86-64 -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

def publicKeyBrainpoolP384r1 : Prog isa := Cfg.publicKey Ecdsa.X86_64.brainpoolp384r1

end VG.Impl.EcKey.X86_64

namespace VG.Impl.EcKey.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ec_brainpoolp384r1_public_key` as emitted: its code, then its cleanup. -/
def publicKeyBrainpoolP384r1 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyBrainpoolP384r1

end VG.Impl.EcKey.X86_64.Fn
