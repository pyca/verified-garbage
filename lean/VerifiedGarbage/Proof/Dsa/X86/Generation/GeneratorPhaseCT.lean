module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGeneratorCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPhase
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Generation.FinishDomainCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGenerator

/-! # A public generator result determines whether final domain validation runs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def generatorExpected (P : PSearchPlan) (value : Nat) : Option Nat := Spec.Dsa.generator value P.qvalue P.hs

def generatorPhaseStatus (P : PSearchPlan) (value : Nat) : BitVec 32 :=
  if (generatorExpected P value).isSome then 1 else 3

def GeneratorPhaseAfter (P : PSearchPlan) (value used : Nat) (s : State) : Prop :=
  ∃ W, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used ∧ W 19 = generatorPhaseStatus P value ∧
    Spec.Rsa.bytesAt s.mem (off P.context.geometry.base p) P.context.geometry.pLen = Spec.Dsa.encodeBE P.context.geometry.pLen value ∧
    ∀ gvalue, generatorExpected P value = some gvalue →
      Spec.Rsa.bytesAt s.mem (off P.context.geometry.base g) P.context.geometry.pLen = Spec.Dsa.encodeBE P.context.geometry.pLen gvalue

theorem generatorPhase_search_ct (P : PSearchPlan) (value used : Nat) :
    RelCT isa (Two fun (_ : Unit) => SearchGeneratorAt P value used) (nativeGenerator P.context.geometry.pLen)
      (Two fun (_ : Unit) => GeneratorPhaseAfter P value used) := by
  refine two_post (searchGenerator_ct P value used) ?_
  rintro _ s ⟨⟨W, R, cursor⟩, A⟩
  refine WP.mono (searchGenerator_ok R A) fun t ⟨Wt, Rt, usedT, pb, outcome, _, _⟩ => ?_
  refine ⟨Wt, Rt, usedT.trans cursor, ?_⟩
  rcases outcome with ⟨status, expected⟩ | ⟨gvalue, status, expected, gb⟩
  · change generatorExpected P value = none at expected
    refine ⟨?_, pb, ?_⟩
    · simpa only [generatorPhaseStatus, expected, Option.isSome_none, Bool.false_eq_true, ite_false] using status
    · intro gvalue good; rw [expected] at good; contradiction
  · change generatorExpected P value = some gvalue at expected
    refine ⟨?_, pb, ?_⟩
    · simpa only [generatorPhaseStatus, expected, Option.isSome_some, ite_true] using status
    · intro other good
      have eq := Option.some.inj (expected.symm.trans good)
      rw [← eq]; exact gb

theorem generatorPhaseAfter_keep {P : PSearchPlan} {value used : Nat} {s t : State}
    (H : GeneratorPhaseAfter P value used s) (mem : t.mem = s.mem) (K : Keeps [.eax] s t) :
    GeneratorPhaseAfter P value used t := by
  obtain ⟨W, R, cursor, status, pb, gb⟩ := H
  have Rt := R.control (by rw [mem]; exact Outside.refl _ _ _ _) (K.mono (by decide))
  exact ⟨W, Rt, cursor, status, by rw [mem]; exact pb, fun v hv => by rw [mem]; exact gb v hv⟩

theorem generatorPhase_ct (F : KeyRandom.CheckCall.CheckFn) (P : PSearchPlan) (value used : Nat) :
    RelCT isa (Two fun (_ : Unit) => SearchGeneratorAt P value used)
      (.seq (nativeGenerator P.context.geometry.pLen)
        (onSuccess (finishDomain F.name F.code P.context.geometry.pLen P.context.geometry.qLen))) (fun _ _ => True) := by
  refine RelCT.seq (generatorPhase_search_ct P value used)
    (onSuccess_ct (fun (_ : Unit) => P.context.geometry.frameBase) (fun _ => generatorPhaseStatus P value) ?_
      (fun _ _ _ H mem K => generatorPhaseAfter_keep H mem K) ?_)
  · rintro _ s ⟨W, R, _, status, _, _⟩
    exact ⟨R.context.arena.frame, (R.context.representation 19 (by decide)).trans status⟩
  · cases expected : generatorExpected P value with
    | none =>
      apply RelCT.of_false
      rintro s t ⟨_, hs, _⟩
      have impossible := hs.2
      simp only [generatorPhaseStatus, expected, Option.isSome_none, Bool.false_eq_true, ite_false] at impossible
      exact (by decide : (3 : BitVec 32) ≠ 1) impossible
    | some gvalue =>
      refine (finishDomain_ct F P.context
        (Spec.Dsa.encodeBE P.context.geometry.pLen value ++ Spec.Dsa.encodeBE P.context.geometry.qLen P.qvalue ++
          Spec.Dsa.encodeBE P.context.geometry.pLen gvalue)).mono (fun _ _ => two_mono ?_) (fun _ _ h => h)
      rintro _ s ⟨⟨W, R, _, _, pb, gb⟩, _⟩
      refine ⟨⟨W, R.context⟩, ?_⟩
      have qb : Spec.Rsa.bytesAt s.mem (off P.context.geometry.base q) P.context.geometry.qLen =
          Spec.Dsa.encodeBE P.context.geometry.qLen P.qvalue := by
        have enc := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt s.mem (off P.context.geometry.base q) P.context.geometry.qLen)
        rw [R.qval] at enc
        simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using enc.symm
      rw [pb, qb, gb gvalue expected]
end VG.Proof.Dsa.X86.Generation
