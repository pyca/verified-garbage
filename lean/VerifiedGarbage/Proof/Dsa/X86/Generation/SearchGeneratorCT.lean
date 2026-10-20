module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGeneratorMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeGeneratorCT

/-! # Generator search shares only live public frame words, never unused stack contents -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def generatorPublicWords (P : PSearchPlan) (used : Nat) : Nat → BitVec 32 :=
  frameUpdate (frameUpdate (frameUpdate P.context.saved 1 P.seed.pointer) 10 P.seedUsed) 16 (BitVec.ofNat 32 used)

def publicGeneratorPlan (P : PSearchPlan) (value used : Nat)
    (D : VG.Proof.Dsa.Generation.PDomain P.context.geometry.pLen value) : GeneratorSearchPlan :=
  P.context.geometry.generatorPlan
    (P.context.geometry.prime P.context.witnesses P.context.geometry.pLen value
      (by have := P.context.geometry.width; omega) (by have := P.context.geometry.width; omega)
      (by rcases P.context.geometry.width with h | h | h <;> rw [h] <;> decide) D.bits D.odd)
    P.context.hs (generatorPublicWords P used) P.qvalue rfl rfl rfl
    P.context.parent P.context.hPointer P.context.hLength

def SearchGeneratorAt (P : PSearchPlan) (value used : Nat) (s : State) : Prop :=
  (∃ W, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used) ∧ PSearchAccepted P value s

theorem searchGenerator_publicMemory {P : PSearchPlan} {value used : Nat}
    (D : VG.Proof.Dsa.Generation.PDomain P.context.geometry.pLen value)
    {s : State} (H : SearchGeneratorAt P value used s) :
    GeneratorStartAt P.context.geometry.pLen (publicGeneratorPlan P value used D) s := by
  obtain ⟨⟨W, R, cursor⟩, A⟩ := H
  have M := searchGeneratorMemory R A
  refine ⟨⟨W, M.prepared, M.layout, M.representation, ?_, M.tapeValue, M.exponentValue,
    M.tapeRead, M.exponentRead, M.outputWrite⟩, rfl⟩
  intro i hi hx
  change W i = generatorPublicWords P used i
  by_cases i16 : i = 16
  · subst i; exact cursor
  by_cases i10 : i = 10
  · subst i; exact R.seedUsed
  by_cases i1 : i = 1
  · subst i; exact R.source
  simp only [generatorPublicWords, frameUpdate, ite_eq_right i16, ite_eq_right i10, ite_eq_right i1]
  apply R.context.fixed i hi
  simp only [parameterMutableSlots, List.mem_cons, List.not_mem_nil, or_false] at *
  omega

theorem searchGenerator_ct (P : PSearchPlan) (value used : Nat) :
    RelCT isa (Two fun (_ : Unit) => SearchGeneratorAt P value used)
      (nativeGenerator P.context.geometry.pLen) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨u, hs, ht⟩ es et
  exact nativeGenerator_ct P.context.geometry.pLen s t ts tt s' t'
    ⟨publicGeneratorPlan P value used hs.2.domain,
      searchGenerator_publicMemory hs.2.domain hs, searchGenerator_publicMemory hs.2.domain ht⟩ es et
end VG.Proof.Dsa.X86.Generation
