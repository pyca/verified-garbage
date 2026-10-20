module

public import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# The DES block's x86 code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here:
the checks of each part (`Round.lean`, `Block.lean`) and the literals of the
functions that run the block (`Lit.lean`) read these literals rather than
evaluate the S-box leaves and bit permutations again.
-/

@[expose] public section

namespace VG

materialize_table Impl.CmacTripleDes.X86.leaf 2 64
materialize_value Impl.CmacTripleDes.X86.inputs
materialize_table Impl.CmacTripleDes.X86.tree 2
materialize_value Impl.CmacTripleDes.X86.output
materialize_value Impl.CmacTripleDes.X86.ipCode
materialize_value Impl.CmacTripleDes.X86.fpCode
materialize_flat_code Impl.CmacTripleDes.X86.block

end VG
