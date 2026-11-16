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

namespace Proof.CmacTripleDes.AArch64

/-- The table's bytes as numbers: a table of numbers is packed in one
(`materialize_table`), in which the kernel reads a byte by a shift, where it
walks a table of `BitVec 8`, a list, to each of the 256 bytes that the
block's code loads (33,000 steps for the block's literal). -/
def sTableN (k : Nat) : Nat := (Impl.CmacTripleDes.AArch64.sTable k).toNat

end Proof.CmacTripleDes.AArch64

materialize_table Proof.CmacTripleDes.AArch64.sTableN 256

namespace Impl.CmacTripleDes.AArch64

/-- The table registers' bytes, read in the packed table (`sTableN.lit`). -/
noncomputable def sTable.lit (k : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (Proof.CmacTripleDes.AArch64.sTableN.lit k)

theorem sTable.lit_eq : sTable = sTable.lit := by
  funext k
  rw [sTable.lit, ← Proof.CmacTripleDes.AArch64.sTableN.lit_eq, Proof.CmacTripleDes.AArch64.sTableN,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Impl.CmacTripleDes.AArch64

materialize_value Impl.CmacTripleDes.AArch64.pGroups
materialize_value Impl.CmacTripleDes.AArch64.ipCode
materialize_value Impl.CmacTripleDes.AArch64.fpCode
materialize_value Impl.CmacTripleDes.AArch64.spreadPre
materialize_code Impl.CmacTripleDes.AArch64.block

end VG
