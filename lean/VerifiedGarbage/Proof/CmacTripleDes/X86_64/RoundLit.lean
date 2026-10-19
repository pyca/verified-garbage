module

public import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# The DES block's x86-64 code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

@[expose] public section

namespace VG

materialize_table Impl.CmacTripleDes.X86_64.leaf 64
materialize_value Impl.CmacTripleDes.X86_64.inputs
materialize_value Impl.CmacTripleDes.X86_64.sboxes
materialize_value Impl.CmacTripleDes.X86_64.output
materialize_value Impl.CmacTripleDes.X86_64.ipCode
materialize_value Impl.CmacTripleDes.X86_64.fpCode
materialize_flat_code Impl.CmacTripleDes.X86_64.block

end VG
