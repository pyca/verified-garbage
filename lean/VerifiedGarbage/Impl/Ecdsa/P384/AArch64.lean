module

public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64.Cfg
public import VerifiedGarbage.Impl.P384.CombArithmetic

/-! # ECDSA over P-384 on AArch64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- `vg_ecdsa_p384_sign`: the comb by Jacobian mixed additions, pipelined in
two passes (`Impl.P384.CombArithmetic.comb`). -/
def signP384 : Prog isa := p384.signWith Impl.P384.CombArithmetic.comb

end VG.Impl.Ecdsa.AArch64
