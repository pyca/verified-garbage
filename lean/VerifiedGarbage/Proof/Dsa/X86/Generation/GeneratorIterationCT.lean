module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchAnswerCT
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchAnswerCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeBlocksCT

/-! # A generator tape iteration has a trace fixed by public cursor and candidate data -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorSearch_check_ct (len : Nat) : RelCT isa (Two (GeneratorSearchBefore len))
    (.block (chunkCheck generatorTape len)) (Two (GeneratorSearchChecked len)) := by
  refine two_piece [.esp] ?_ (chunkCheck_check _ len (.inr rfl)) (fun _ _ H => generatorSearch_check H)
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨Ws, Rs, _⟩ := hs.1
  obtain ⟨Wt, Rt, _⟩ := ht.1
  exact BitVec.eq_of_toNat_eq (Rs.layout.esp_toNat.trans Rt.layout.esp_toNat.symm)

theorem generatorSearch_take_ct (len : Nat) : RelCT isa (Two (GeneratorSearchAvailable len))
    (.block (tapeTake generatorTape len)) (Two (GeneratorSearchTaken len)) := by
  refine two_piece [.esp] ?_ (tapeTake_check _ len (.inr rfl)) (fun _ _ H => generatorSearch_take H)
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨Ws, Rs, _⟩ := hs.1.1
  obtain ⟨Wt, Rt, _⟩ := ht.1.1
  exact BitVec.eq_of_toNat_eq (Rs.layout.esp_toNat.trans Rt.layout.esp_toNat.symm)

theorem generatorIteration_ct (len : Nat) : RelCT isa (Two (GeneratorSearchBefore len))
    (tapeIteration generatorTape len (generatorBody len)) (fun _ _ => True) := by
  unfold tapeIteration
  refine RelCT.seq (generatorSearch_check_ct len) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · refine two_taint [.esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs, _⟩ := hs.1.1.1
    obtain ⟨Wt, Rt, _⟩ := ht.1.1.1
    exact BitVec.eq_of_toNat_eq (Rs.layout.esp_toNat.trans Rt.layout.esp_toNat.symm)
  · refine RelCT.seq ((generatorSearch_take_ct len).mono
      (fun _ _ => two_mono (fun _ _ h => generatorSearch_available h.1 h.2)) (fun _ _ h => h))
      (RelCT.seq (generatorSearch_answer_ct len) ?_)
    refine two_taint [.esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs, _, _⟩ := hs.1
    obtain ⟨Wt, Rt, _, _⟩ := ht.1
    exact BitVec.eq_of_toNat_eq (Rs.layout.esp_toNat.trans Rt.layout.esp_toNat.symm)
end VG.Proof.Dsa.X86.Generation
