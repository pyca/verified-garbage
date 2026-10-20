module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of the 16-bit NTT and its inverse, for the checks the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_code ntt
materialize_code nttInv

end VG.Impl.MlKem.AArch64.Ntt16
