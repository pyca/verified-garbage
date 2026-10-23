module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE

/-! # brainpoolP384r1 public keys on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp384r1_public_key`. -/
def publicKeyBrainpoolP384r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.brainpoolp384r1

end VG.Impl.EcKey.PPC64LE
