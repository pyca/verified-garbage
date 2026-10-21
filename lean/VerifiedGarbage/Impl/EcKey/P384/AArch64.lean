module

public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-! # P-384 public keys on AArch64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.AArch64

open VG.AArch64

/-- `vg_ec_p384_public_key`: the comb by Jacobian mixed additions, pipelined in
two passes (`Impl.P384.CombArithmetic.comb`). -/
def publicKeyP384 : Prog isa :=
  Cfg.publicKeyWith Impl.Ecdsa.AArch64.p384 Impl.P384.CombArithmetic.comb

end VG.Impl.EcKey.AArch64
