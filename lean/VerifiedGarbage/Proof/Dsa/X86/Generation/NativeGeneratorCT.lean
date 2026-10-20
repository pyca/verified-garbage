module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLoopCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeBlocksCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl

/-! # A generator search restarts at the public beginning of its finite h tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def GeneratorStartAt (len : Nat) (P : GeneratorSearchPlan) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory P W s) ∧ P.core.len = len

def generatorStart (P : GeneratorSearchPlan) : GeneratorSearchPublic := ⟨P, 0, Nat.zero_le _⟩

theorem generatorReset_ct (len : Nat) : RelCT isa (Two (GeneratorStartAt len))
    (.block (tapeReset generatorTape)) (Two fun P => GeneratorSearchBefore len (generatorStart P)) := by
  refine two_piece [.esp] ?_ (tapeReset_check _ (.inr rfl)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs⟩ := hs.1
    obtain ⟨Wt, Rt⟩ := ht.1
    exact BitVec.eq_of_toNat_eq (Rs.layout.esp_toNat.trans Rt.layout.esp_toNat.symm)
  · rintro P s ⟨⟨W, R⟩, width⟩
    refine WP.mono (tapeReset_ok R.layout R.representation generatorTape (by decide)) fun t ⟨_, Wt, O, K⟩ => ?_
    have Rt := R.control Wt (by
      intro i _ hx
      have ne : i ≠ 20 := by intro eq; subst i; simp at hx
      change frameUpdate W 20 0 i = W i
      simp only [frameUpdate, ite_eq_right ne]) O (by unfold generatorTape VG.Impl.Dsa.X86.Generation.frameBytes; decide) K (by decide)
    exact ⟨⟨_, Rt, rfl⟩, width⟩

theorem nativeGenerator_ct (len : Nat) : RelCT isa (Two (GeneratorStartAt len))
    (nativeGenerator len) (fun _ _ => True) :=
  RelCT.seq (generatorReset_ct len)
    (two_map generatorStart (fun _ _ h => h) (generatorLoop_ct len))
end VG.Proof.Dsa.X86.Generation
