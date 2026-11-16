module

public import VerifiedGarbage.Proof.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Axioms
import Mathlib.Tactic.ToExpr
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import Mathlib.Tactic.ToExpr
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower

/-!
# The scalar rounds: what they keep

What the scalar rounds keep besides `Boundary.CoreState`, the middle's
contract in `wrap_correct`: memory, and the AdvSIMD registers other than
the core's temporaries (`RoundKeep`), which the registers the boundary
saves and the callee-saved ones are not among (`savedVec_not_temps`,
`preservedV_not_temps`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

theorem savedVec_not_temps : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v24 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v25 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v28 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v29 := by decide

theorem preservedV_not_temps : ∀ r ∈ preservedV, r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v28 ∧ r ≠ .v29 := by
  decide

/-- What the rounds keep besides the boundary's invariant: memory, and the
AdvSIMD registers other than the core's temporaries. -/
structure RoundKeep (s t : State) : Prop where
  mem : t.mem = s.mem
  v : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

end VG.Proof.Sha3.AArch64.Scalar
