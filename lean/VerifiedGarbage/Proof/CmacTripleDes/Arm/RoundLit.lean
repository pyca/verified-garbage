module

public import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-!
# The DES block's 32-bit ARM code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

@[expose] public section

namespace VG

materialize_table Impl.CmacTripleDes.Arm.leaf 2 64
materialize_value Impl.CmacTripleDes.Arm.inputs

/-- Half `h`'s tree. -/
abbrev Proof.CmacTripleDes.Arm.sbCode (h : Nat) : List VG.Arm.Instr :=
  Impl.CmacTripleDes.Arm.mux h 6 0 .r0

materialize_table Proof.CmacTripleDes.Arm.sbCode 2
materialize_value Impl.CmacTripleDes.Arm.sboxes
materialize_value Impl.CmacTripleDes.Arm.output
materialize_value Impl.CmacTripleDes.Arm.ipCode
materialize_value Impl.CmacTripleDes.Arm.fpCode
materialize_flat_code Impl.CmacTripleDes.Arm.block

end VG
