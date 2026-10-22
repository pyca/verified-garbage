module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.FastInv
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.FastInv
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of `vg_mlkem16_inv_ntt` (mlkem-native's schedule), for the checks the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.FastInv

materialize_code invFast
materialize_value tab

end VG.Impl.MlKem.AArch64.Ntt16.FastInv

namespace VG.Proof.MlKem.AArch64.NttR

/-- The table of `invFast`. -/
def tabFIT : Nat := packH Impl.MlKem.AArch64.Ntt16.FastInv.tab

materialize_value tabFIT

end VG.Proof.MlKem.AArch64.NttR
