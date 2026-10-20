module

public import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The DES block's AArch64 code as literals, for kernel-evaluated checks

The tables, the groups of `P`, `IP`, `IP⁻¹` and the block are each evaluated
once, here: the checks of each part (`Layout.lean`, `Round.lean`,
`Block.lean`) and the literals of the functions that run the block
(`Lit.lean`) read these literals rather than evaluate the S-boxes and bit
permutations again.
-/

@[expose] public section

namespace VG

materialize_table Impl.CmacTripleDes.AArch64.sTable 256
materialize_value Impl.CmacTripleDes.AArch64.pGroups
materialize_value Impl.CmacTripleDes.AArch64.ipCode
materialize_value Impl.CmacTripleDes.AArch64.fpCode
materialize_value Impl.CmacTripleDes.AArch64.spreadPre
materialize_code Impl.CmacTripleDes.AArch64.block

end VG
