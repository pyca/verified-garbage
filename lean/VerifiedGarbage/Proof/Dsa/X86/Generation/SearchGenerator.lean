module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorWrites
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeGenerator

/-! # Run generator search in the persistent parameter frame and preserve p and q -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem searchGenerator_ok {P : PSearchPlan} {value : Nat} {W : Nat → BitVec 32} {s : State}
    (R : PSearchMemory P W s) (A : PSearchAccepted P value s) :
    WP isa (nativeGenerator P.context.geometry.pLen) s fun t =>
      let expected := Spec.Dsa.generator value P.qvalue
        ((Spec.Dsa.generationChunks P.context.geometry.pLen P.context.hs.bytes).map Spec.Dsa.decodeBE)
      ∃ W', PSearchMemory P W' t ∧ W' 16 = W 16 ∧
        Spec.Rsa.bytesAt t.mem (off P.context.geometry.base p) P.context.geometry.pLen =
          Spec.Dsa.encodeBE P.context.geometry.pLen value ∧
        ((W' 19 = 3 ∧ expected = none) ∨ ∃ gvalue, W' 19 = 1 ∧ expected = some gvalue ∧
          Spec.Rsa.bytesAt t.mem (off P.context.geometry.base g) P.context.geometry.pLen =
            Spec.Dsa.encodeBE P.context.geometry.pLen gvalue) ∧
        Frame (generationGeneratorWrites P.context.geometry) s.mem t.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := P.context.geometry.width
  have qw := P.context.geometry.qWidth
  have qr : q + P.context.geometry.qLen ≤ usedBytes P.context.geometry.pLen := by unfold q usedBytes domainCheck; omega
  have pr : p + P.context.geometry.pLen ≤ usedBytes P.context.geometry.pLen := by unfold p usedBytes domainCheck; omega
  refine WP.mono (nativeGenerator_ok (searchGeneratorMemory R A)) fun t ⟨Wt, Rt, result, O, rd, wr⟩ => ?_
  rw [searchGeneratorWrites R A] at O
  have sp : t.gpr .esp = s.gpr .esp := BitVec.eq_of_toNat_eq
    (Rt.layout.esp_toNat.trans R.context.arena.frame.esp_toNat.symm)
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := ⟨by
    intro r hr
    cases r <;> first | exact sp | exact False.elim (hr (by decide)), rd, wr⟩
  have F := O.sub (generatorWrites_mutable P.context.geometry)
  have context := R.context.frame Rt.representation (by
    intro i hi hx
    apply Rt.fixed i hi
    intro bad
    have subset : [0, 2, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36].Subset parameterMutableSlots := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [parameterMutableSlots, List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact hx (subset bad)) F Kt (by decide)
  have source : Wt 1 = P.seed.pointer := (Rt.fixed 1 (by decide) (by decide)).trans R.source
  have qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off P.context.geometry.base q) P.context.geometry.qLen) = P.qvalue := by
    rw [drawFrame_bytes O (generatorWrites_bufferApart _ qr (by unfold q g; omega)) (by omega), R.qval]
  refine ⟨Wt, ⟨context, R.seed.keep F P.seed.parameterApart Kt, source, qval, (Rt.fixed 10 (by decide) (by decide)).trans R.seedUsed⟩,
    Rt.fixed 16 (by decide) (by decide), ?_, ?_, O, Kt⟩
  · rw [drawFrame_bytes O (generatorWrites_bufferApart _ pr (by unfold p g; omega)) (by omega), A.pBytes]
  · rcases result with failed | ⟨gvalue, status, expected, bytes⟩
    · exact .inl ⟨failed.1, by simpa only [GeneratorSearchPlan.remaining, searchGeneratorPlan, GenerationGeometry.generatorPlan, PSearchAccepted.core, GenerationGeometry.prime, List.drop_zero] using failed.2⟩
    · refine .inr ⟨gvalue, status, ?_, ?_⟩
      · simpa only [GeneratorSearchPlan.remaining, searchGeneratorPlan, GenerationGeometry.generatorPlan, PSearchAccepted.core, GenerationGeometry.prime, List.drop_zero] using expected
      · change Spec.Rsa.bytesAt t.mem ((P.context.geometry.pointer g).setWidth 64) P.context.geometry.pLen = _ at bytes
        rw [P.context.geometry.pointer_addr (by unfold g usedBytes domainCheck; omega)] at bytes
        exact bytes
end VG.Proof.Dsa.X86.Generation
