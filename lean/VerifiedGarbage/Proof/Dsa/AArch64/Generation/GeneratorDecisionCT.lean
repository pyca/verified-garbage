module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRangePlanCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRangePlanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorOutput
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Generator decisions branch on masks determined by public generation inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

def GeneratorMasked (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ s.gpr .x3 = mask (valid p)

theorem generatorStatus_ct (len : Nat) (status : Nat) (hs : status = 1 ∨ status = 3) :
    RelCT isa (Two (GeneratorBefore len)) (.block (stackStatus status)) (fun _ _ => True) := by
  rcases hs with rfl | rfl <;>
    exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

def GeneratorPlan.inputValid (p : GeneratorPlan) : Bool :=
  decide (1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1)

def GeneratorPlan.outputValid (p : GeneratorPlan) : Bool := decide (1 < p.value)

theorem generatorInputRange_mask {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorRangeFromFrame len false) s (GeneratorMasked len GeneratorPlan.inputValid p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorInputRange_ok h
  rw [he] at step
  exact WP.mono step fun t ⟨hr, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, hr⟩

theorem generatorOutputRange_mask {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorOutputBefore len p s) :
    WP isa (generatorRangeFromFrame len true) s (GeneratorMasked len GeneratorPlan.outputValid p) := by
  obtain ⟨⟨⟨W, h⟩, he⟩, hg⟩ := h
  have step := generatorOutputRange_ok h hg
  rw [he] at step
  exact WP.mono step fun t ⟨hr, ht, _, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, hr⟩

theorem generatorEvaluate_ready (M : Mont)  {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorEvaluate M.mm len) s (GeneratorOutputBefore len p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorEvaluateStage_ok M h
  rw [he] at step
  exact WP.mono step fun t ⟨hg, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, by simpa only [he] using hg⟩

end VG.Proof.Dsa.AArch64.Generation
