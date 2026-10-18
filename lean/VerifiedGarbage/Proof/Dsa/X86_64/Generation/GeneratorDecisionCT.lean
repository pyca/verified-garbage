module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRangePlanCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus

/-! # Generator decisions branch on masks determined by public generation inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

def GeneratorMasked (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ s.gpr .rax = mask (valid p)

def GeneratorDecided (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ isa.eval .e s = !(valid p)

theorem generatorTest_ct (len : Nat) (valid : GeneratorPlan → Bool) :
    RelCT isa (Two (GeneratorMasked len valid)) (.block [.alu .test .rax (.reg .rax)])
      (Two (GeneratorDecided len valid)) := by
  refine two_piece [.rax] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s ⟨⟨⟨W, h⟩, he⟩, hr⟩
    refine WP.mono (generatorTest_ok h hr) fun t ⟨hz, ht, _, _⟩ => ?_
    exact ⟨⟨⟨W, ht⟩, he⟩, by simp only [eval, hz]⟩

theorem generatorStatus_ct (len : Nat) (status : Nat) (hs : status = 1 ∨ status = 3) :
    RelCT isa (Two (GeneratorBefore len)) (.block (stackStatus status)) (fun _ _ => True) := by
  have pins : Pins (GeneratorBefore len) [.rsp] := by
    intro p s t ⟨⟨Ws, hs⟩, _⟩ ⟨⟨Wt, ht⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  rcases hs with rfl | rfl <;> exact two_taint [.rsp] pins (by taint_decide)

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

theorem generatorEvaluate_ready (M : Mont) (Sq : MontS) {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorEvaluate Sq.mm M.mm len) s (GeneratorOutputBefore len p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorEvaluateStage_ok M Sq h
  rw [he] at step
  exact WP.mono step fun t ⟨hg, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, by simpa only [he] using hg⟩

end VG.Proof.Dsa.X86_64.Generation
