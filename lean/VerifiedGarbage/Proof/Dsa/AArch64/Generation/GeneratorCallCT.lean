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

/-- The facts the stage's entry needs, of a public p and q. -/
structure GeneratorInputs (a : SeedGeneratorPublic) (s : State) : Prop where
  memory : ∃ W, GenerationMemory a.seed.context W s
  p : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p)
    a.seed.context.geo.pLen = Spec.Dsa.encodeBE a.seed.context.geo.pLen a.value
  exponent : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.seed.context.geo.B exponent) a.seed.context.geo.pLen =
    Spec.Dsa.encodeBE a.seed.context.geo.pLen ((a.value - 1) / a.qValue)
  q : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.seed.context.geo.B q) a.seed.context.geo.qLen =
    Spec.Dsa.encodeBE a.seed.context.geo.qLen a.qValue

theorem SeedGeneratorPublic.q_bounds (a : SeedGeneratorPublic) :
    0 < a.qValue ∧ a.qValue < 256 ^ a.seed.context.geo.qLen := by
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases a.seed.context.geo.qWidth with hh | hh <;> omega : 2 ≤ 8 * a.seed.context.geo.qLen) a.seed.seed.bytes
  refine ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1, ?_⟩
  have := shape.2.2
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  exact this

/-- The arguments in their registers. -/
def GeneratorReady (pLen : Nat) (a : SeedGeneratorPublic) (u : State) : Prop :=
  a.seed.context.geo.pLen = pLen ∧ ∃ s, GeneratorInputs a s ∧ u.gpr .x0 = a.seed.context.geo.B ∧
    u.gpr .x1 = BitVec.ofNat 64 (usedBytes a.seed.context.geo.pLen / 8) ∧
    u.gpr .x2 = a.seed.context.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 a.seed.context.hs.bytes.length ∧
    u.mem = s.mem ∧ u.sp = a.seed.context.geo.F ∧ u.rd = s.rd ∧ u.wr = s.wr

theorem GeneratorReady.entry {pLen : Nat} {a : SeedGeneratorPublic} {u : State} (h : GeneratorReady pLen a u) :
    GeneratorEntry a.seed.context a.value a.qValue u := by
  obtain ⟨_, s, ⟨⟨W, hm⟩, bp, be, bq⟩, h0, h1, h2, h3, hmem, hsp, hrd, hwr⟩ := h
  exact generatorCall_entry hm a.value a.qValue a.domain a.q_bounds.2 a.q_bounds.1 bp be bq h0 h1 h2 h3 hmem hsp hrd hwr

end VG.Proof.Dsa.AArch64.Generation
