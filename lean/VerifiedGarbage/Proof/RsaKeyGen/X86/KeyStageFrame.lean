module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop

/-! ### `RsaKeyGen.X86.KeyExponentFrame`, which this module and modules that import it used -/

section

/-! # Frames for the native private-exponent arithmetic

The public exponent, the LCM, the sorted factors, and the constant one
survive the temporary bank. Only four persistent working arrays change.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def exponentTemps (n : Nat) : List (Nat × Nat) := [(kOk, 68), (hdr, 15 * S n)]
def exponentArrays : List Nat := [aD, aDen, aU, aV]
def exponentRanges (n : Nat) : List (Nat × Nat) := exponentTemps n ++ ranges n exponentArrays []

theorem exponent_temps_keep {m m' : Mem} {B : Addr} {k n : Nat} {js ds : List Nat}
    (width : k ≤ n) (arrays : ∀ j ∈ js, j < 15)
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 68) (O : Keep B k js ds m m') :
    Outs B (exponentTemps n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentTemps], ?_, ?_⟩
    · unfold arr
      omega_using []
    · have endK := arr_end (w := k) (arrays j hj)
      have growth : arr k 15 ≤ arr n 15 := by unfold arr S; omega_using [width]
      have E : arr n 15 = hdr + 15 * S n := rfl
      rw [E] at growth
      omega
  · exact ⟨(kOk, 68), by simp [exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

theorem exponent_temps_inverse {m m' : Mem} {B : Addr} {k n : Nat} (width : k ≤ n)
    (O : Outs B (inverseRanges k invSlots) m m') : Outs B (exponentTemps n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨(hdr, 15 * S n), by simp [exponentTemps], Nat.le_refl _, ?_⟩
    unfold S
    omega
  all_goals exact ⟨(kOk, 68), by simp [exponentTemps], by decide, by decide⟩

theorem exponent_temps_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (exponentTemps n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega_using [fit])
  intro r hr
  simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have lower : hdr ≤ arr n j := Nat.le_add_right ..
    exact Or.inr (Nat.le_trans (by decide : kOk + 68 ≤ hdr) lower)
  · exact Or.inr (arr_mono persistent)

theorem exponent_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (unchanged : ∀ a ∈ exponentArrays, j ≠ a)
    (fit : arr n j + S n ≤ 2 ^ 64) (O : Outs B (exponentRanges n) m m') :
    num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega_using [fit])
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · have lower : hdr ≤ arr n j := Nat.le_add_right ..
      exact Or.inr (Nat.le_trans (by decide : kOk + 68 ≤ hdr) lower)
    · exact Or.inr (arr_mono persistent)
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, ha, rfl⟩ := output
    have D := arr_disj (w := n) (unchanged a ha)
    simp only at D ⊢
    unfold S at D ⊢
    omega_using [D]

theorem exponent_preserves_e {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (exponentRanges n) m m') : val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · exact Or.inl (by decide : kEv + 8 ≤ kOk)
    · exact Or.inl (by decide : kEv + 8 ≤ hdr)
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, _, rfl⟩ := output
    have lower : hdr ≤ arr n a := Nat.le_add_right ..
    exact Or.inl (Nat.le_trans (by decide : kEv + 8 ≤ hdr) lower)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Frames for key-assembly stages that share the native inverse bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def stageRanges (n : Nat) (js : List Nat) : List (Nat × Nat) :=
  exponentTemps n ++ ranges n js []

theorem stage_mono {m m' : Mem} {B : Addr} {n : Nat} {js ks : List Nat}
    (included : ∀ j ∈ js, j ∈ ks) (O : Outs B (stageRanges n js) m m') :
    Outs B (stageRanges n ks) m m' := by
  refine O.mono ?_
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · exact List.mem_append_left _ temp
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨j, hj, rfl⟩ := output
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨j, included j hj, rfl⟩))

theorem stage_preserves_header {m m' : Mem} {B : Addr} {n d count : Nat} {js : List Nat}
    (bound : d + 4 * count ≤ kOk) (O : Outs B (stageRanges n js) m m') :
    val32 m' B d count = val32 m B d count := by
  apply O.val32 _ (by unfold kOk at bound; omega_using [bound])
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · exact Or.inl bound
    · exact Or.inl (Nat.le_trans bound (by decide : kOk ≤ hdr))
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, _, rfl⟩ := output
    exact Or.inl (Nat.le_trans bound (Nat.le_trans (by decide : kOk ≤ hdr) (Nat.le_add_right ..)))

theorem stage_preserves_e {m m' : Mem} {B : Addr} {n : Nat} {js : List Nat}
    (O : Outs B (stageRanges n js) m m') : val32 m' B kEv 2 = val32 m B kEv 2 :=
  stage_preserves_header (by decide) O

theorem stage_temps {m m' : Mem} {B : Addr} {n : Nat} {js : List Nat}
    (O : Outs B (exponentTemps n) m m') : Outs B (stageRanges n js) m m' :=
  O.mono (fun _ hr => List.mem_append_left _ hr)

theorem stage_keep {m m' : Mem} {B : Addr} {n k : Nat} {js is ds : List Nat}
    (width : k ≤ n) (arrays : ∀ j ∈ is, j < 15 ∨ (k = n ∧ j ∈ js))
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 68) (O : Keep B k is ds m m') :
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
  · exact ⟨(kOk, 68), by simp [stageRanges, exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

theorem stage_inverse {m m' : Mem} {B : Addr} {n k : Nat} {js : List Nat} (width : k ≤ n)
    (O : Outs B (inverseRanges k invSlots) m m') : Outs B (stageRanges n js) m m' :=
  stage_temps (exponent_temps_inverse width O)

theorem stage_outside {m m' : Mem} {B : Addr} {n j : Nat} {js : List Nat}
    (output : j ∈ js) (O : Outside B (arr n j) (S n) m m') : Outs B (stageRanges n js) m m' :=
  Outs.of_outside O (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, output, rfl⟩)))

theorem stage_preserves_num {m m' : Mem} {B : Addr} {n j : Nat} {js : List Nat}
    (persistent : 15 ≤ j) (unchanged : j ∉ js) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (stageRanges n js) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega_using [fit])
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · exact Or.inr (Nat.le_trans (by decide : kOk + 68 ≤ hdr) (Nat.le_add_right ..))
    · exact Or.inr (arr_mono persistent)
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, ha, rfl⟩ := output
    have D := arr_disj (w := n) (show j ≠ a from fun E => unchanged (E ▸ ha))
    simp only at D ⊢
    unfold S at D ⊢
    omega_using [D]

end VG.Proof.RsaKeyGen.X86.Key
