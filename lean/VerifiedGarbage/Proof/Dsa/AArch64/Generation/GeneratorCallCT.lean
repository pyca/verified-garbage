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

theorem generatorCall_ct (G : GeneratorStage) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore pLen qLen)) (Impl.Dsa.AArch64.Generation.generatorCall G.run pLen)
      fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.generatorCall
  -- The arguments.
  have args : RelCT isa (Two (SeedGeneratorBefore pLen qLen))
      (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) (Two (GeneratorReady pLen)) := by
    have wp : ∀ a s, SeedGeneratorBefore pLen qLen a s →
        WP isa (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) s (GeneratorReady pLen a) := by
      intro a s ⟨⟨⟨⟨W, hm, _⟩, _, _⟩, hp, bq⟩, bp, be⟩
      subst hp
      exact WP.mono (generatorCallArgs_ok hm) fun u ⟨h0, h1, h2, h3, hmem, ku⟩ =>
        ⟨rfl, s, ⟨⟨W, hm⟩, bp, be, bq⟩, h0, h1, h2, h3, hmem, ku.sp.trans hm.layout.sp, ku.rd, ku.wr⟩
    rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide) wp
  -- The call.
  have hb : Generator.Supported pLen := by rcases sizes with h | h | h <;> simp [h.1, Generator.Supported]
  have call : RelCT isa (Two (GeneratorReady pLen)) (G.run pLen)
      (Two fun (_ : SeedGeneratorPublic) (_ : State) => True) := by
    refine two_post ?_ fun a u h => ?_
    · refine RelCT.callEx (G.verified pLen hb).1 (G.verified pLen hb).2.1 fun u₁ u₂ ⟨a, h₁, h₂, _⟩ => ?_
      have E₁ := h₁.entry
      have E₂ := h₂.entry
      obtain ⟨hp, s₁, _, h0₁, h1₁, h2₁, h3₁, _, hsp₁, _, _⟩ := h₁
      obtain ⟨_, s₂, _, h0₂, h1₂, h2₂, h3₂, _, hsp₂, _, _⟩ := h₂
      subst hp
      refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes⟩
      sig_pub [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
      rw [hsp₁, hsp₂, h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂]
      have hl : (BitVec.ofNat 64 a.seed.context.hs.bytes.length).toNat = a.seed.context.hs.bytes.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.seed.context.hs.size]
      rw [hl, E₁.pv, E₂.pv, E₁.qv, E₂.qv, E₁.tape, E₂.tape]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨hp, s, ⟨⟨W, hm⟩, bp, be, bq⟩, h0, h1, h2, h3, hmem, hsp, hrd, hwr⟩ := h
      subst hp
      exact WP.mono (generatorCall_call_ok G hm a.value a.qValue a.domain a.q_bounds.2 a.q_bounds.1 bp be bq
        h0 h1 h2 h3 hmem hsp hrd hwr) fun _ _ => True.intro
  refine RelCT.seq args (RelCT.seq call ?_)
  exact two_taint [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
