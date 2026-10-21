module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Literals of `vg_mlkem16_ntt` (mlkem-native's schedule), for the checks the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16.Fast

materialize_code fwdFast
materialize_value tab

end VG.Impl.MlKem.AArch64.Ntt16.Fast

namespace VG.Proof.MlKem.AArch64.NttR

/-- Halfwords `L` as constants, halfword `i` in lane `i % 8` of chunk `i / 8`. -/
def packH (L : List Nat) : Nat := L.foldr (fun h acc => cT h + 2 ^ tw * acc) 0

/-- The table of `fwdFast`. -/
def tabFT : Nat := packH Impl.MlKem.AArch64.Ntt16.Fast.tab

materialize_value tabFT

end VG.Proof.MlKem.AArch64.NttR
