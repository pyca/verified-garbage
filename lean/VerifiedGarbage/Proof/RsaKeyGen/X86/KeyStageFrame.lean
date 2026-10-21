module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArrayDivision
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # Frames for key-assembly stages that share the native inverse bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def stageRanges (n : Nat) (js : List Nat) : List (Nat × Nat) :=
  exponentTemps n ++ ranges n js []

theorem stage_temps {m m' : Mem} {B : Addr} {n : Nat} {js : List Nat}
    (O : Outs B (exponentTemps n) m m') : Outs B (stageRanges n js) m m' :=
  O.mono (fun _ hr => List.mem_append_left _ hr)

theorem stage_keep {m m' : Mem} {B : Addr} {n k : Nat} {js is ds : List Nat}
    (width : k ≤ n) (arrays : ∀ j ∈ is, j < 15 ∨ (k = n ∧ j ∈ js))
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 44) (O : Keep B k is ds m m') :
    Outs B (stageRanges n js) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · rcases arrays j hj with temp | ⟨rfl, result⟩
    · refine ⟨(hdr, 15 * S n), by simp [stageRanges, exponentTemps], Nat.le_add_right .., ?_⟩
      have small := inverse_end_le width (Nat.le_refl 15)
      have last := arr_end (w := k) temp
      change arr k j + S k ≤ arr n 15
      exact Nat.le_trans last small
    · exact ⟨(arr k j, S k), List.mem_append_right _
        (List.mem_append_left _ (List.mem_map.mpr ⟨j, result, rfl⟩)), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(kOk, 44), by simp [stageRanges, exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

theorem stage_inverse {m m' : Mem} {B : Addr} {n k : Nat} {js : List Nat} (width : k ≤ n)
    (O : Outs B (inverseRanges k invSlots) m m') : Outs B (stageRanges n js) m m' :=
  stage_temps (exponent_temps_inverse width O)

theorem stage_outside {m m' : Mem} {B : Addr} {n j : Nat} {js : List Nat}
    (output : j ∈ js) (O : Outside B (arr n j) (S n) m m') : Outs B (stageRanges n js) m m' :=
  Outs.of_outside O (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, output, rfl⟩)))

theorem stage_division {m m' : Mem} {B : Addr} {n q r : Nat} {js : List Nat}
    (hq : q ∈ js) (hr : r ∈ js) (O : Outs B (arrayDivisionRanges n q r) m m') :
    Outs B (stageRanges n js) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact ⟨(hdr, 15 * S n), by simp [stageRanges, exponentTemps], Nat.le_refl _, by omega⟩
  · exact ⟨(arr n q, S n), List.mem_append_right _
      (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩)), Nat.le_refl _, by unfold S; omega⟩
  · exact ⟨(arr n r, S n), List.mem_append_right _
      (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)), Nat.le_refl _, by unfold S; omega⟩

theorem stage_preserves_num {m m' : Mem} {B : Addr} {n j : Nat} {js : List Nat}
    (persistent : 15 ≤ j) (unchanged : j ∉ js) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (stageRanges n js) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · exact Or.inr (Nat.le_trans (by decide : kOk + 44 ≤ hdr) (Nat.le_add_right ..))
    · exact Or.inr (arr_mono persistent)
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, ha, rfl⟩ := output
    have D := arr_disj (w := n) (show j ≠ a from fun E => unchanged (E ▸ ha))
    simp only at D ⊢
    unfold S at D ⊢
    omega

end VG.Proof.RsaKeyGen.X86.Key
