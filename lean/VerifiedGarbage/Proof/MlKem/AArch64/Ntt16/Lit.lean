module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Literals of the 16-bit NTT and its inverse, for the checks the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_code ntt
materialize_code nttInv

end VG.Impl.MlKem.AArch64.Ntt16
