module

public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.Generation.Search
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete-chunk tape traversal matches parameter-generation inputs -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem generationChunks_done {width : Nat} {bytes : List Byte} (h : bytes.length < width) :
    Spec.Dsa.generationChunks width bytes = [] := by
  simp [Spec.Dsa.generationChunks, Nat.div_eq_of_lt h]

theorem generationChunks_step {width : Nat} {bytes : List Byte}
    (hw : 0 < width) (h : width ≤ bytes.length) :
    Spec.Dsa.generationChunks width bytes =
      bytes.take width :: Spec.Dsa.generationChunks width (bytes.drop width) := by
  have hdiv : bytes.length / width = (bytes.length - width) / width + 1 := by
    have he : bytes.length = (bytes.length - width) + width := by omega
    exact (congrArg (fun n => n / width) he).trans (Nat.add_div_right _ hw)
  unfold Spec.Dsa.generationChunks
  rw [hdiv, List.range_succ_eq_map]
  simp only [List.map_cons, Nat.zero_mul, List.drop_zero, List.map_map, List.length_drop]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def, Nat.succ_mul, List.drop_drop, Nat.add_comm]

theorem generator_chunks_step {width p q : Nat} {bytes : List Byte}
    (hw : 0 < width) (h : width ≤ bytes.length) :
    Spec.Dsa.generator p q ((Spec.Dsa.generationChunks width bytes).map Spec.Dsa.decodeBE) =
      let candidate := Spec.Dsa.decodeBE (bytes.take width)
      let value := Spec.Dsa.powMod candidate ((p - 1) / q) p
      if 1 < candidate ∧ candidate < p - 1 ∧ 1 < value then some value
      else Spec.Dsa.generator p q ((Spec.Dsa.generationChunks width (bytes.drop width)).map Spec.Dsa.decodeBE) := by
  rw [generationChunks_step hw h, List.map_cons, generator_cons]
  dsimp only
  by_cases hi : 1 < Spec.Dsa.decodeBE (bytes.take width) ∧ Spec.Dsa.decodeBE (bytes.take width) < p - 1
  · by_cases ho : 1 < Spec.Dsa.powMod (Spec.Dsa.decodeBE (bytes.take width)) ((p - 1) / q) p <;>
      simp only [hi, ho, and_true, and_false, ite_true, ite_false]
  · have hn : ¬ (1 < Spec.Dsa.decodeBE (bytes.take width) ∧ Spec.Dsa.decodeBE (bytes.take width) < p - 1 ∧
        1 < Spec.Dsa.powMod (Spec.Dsa.decodeBE (bytes.take width)) ((p - 1) / q) p) :=
      fun hh => hi ⟨hh.1, hh.2.1⟩
    simp only [hi, hn, ite_false]

end VG.Proof.Dsa.Generation
