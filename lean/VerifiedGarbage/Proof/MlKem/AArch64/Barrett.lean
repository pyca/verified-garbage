module

public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM on AArch64: the tables

The tables of the code are those of the standard (`zetaTable_eq`,
`gammaTable_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

end VG.Proof.MlKem.AArch64
