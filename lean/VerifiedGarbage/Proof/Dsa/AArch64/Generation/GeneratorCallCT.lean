module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorPlanCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.GeneratorStageContract

/-! # Calling the generator stage in constant time

The stage's arguments are the generation's pointers and lengths, and its
leak, p, q and the h tape, is public. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout

theorem SeedGeneratorPublic.q_bounds (a : SeedGeneratorPublic) :
    0 < a.qValue ∧ a.qValue < 256 ^ a.seed.context.geo.qLen := by
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases a.seed.context.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * a.seed.context.geo.qLen) a.seed.seed.bytes
  refine ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1, ?_⟩
  have := shape.2.2
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  exact this

end VG.Proof.Dsa.AArch64.Generation
