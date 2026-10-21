module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of the 16-bit NTT with an immutable table, for the runs the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.Readonly

materialize_code fwd
materialize_code fwdW

end VG.Impl.MlKem.AArch64.Ntt16.Readonly

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_value tableHalves

end VG.Impl.MlKem.AArch64.Ntt16

namespace VG.Proof.MlKem.AArch64.NttR

materialize_table zetaN 128

/-- The table of zetas of `fwd` and `fwdW`, halfword `i` the constant in lane
`i` (chunk `i / 8`'s lane `i % 8`). -/
def tabT : Nat := Impl.MlKem.AArch64.Ntt16.tableHalves.foldr (fun h acc => cT h + 2 ^ tw * acc) 0

materialize_value tabT

end VG.Proof.MlKem.AArch64.NttR
