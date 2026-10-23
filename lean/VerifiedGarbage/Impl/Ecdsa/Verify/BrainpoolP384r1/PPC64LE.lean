module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE

/-! # `vg_ecdsa_brainpoolp384r1_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.brainpoolp384r1

end VG.Impl.Ecdsa.Verify.PPC64LE
