module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # Frames for the native private-exponent arithmetic

The public exponent, the LCM, the sorted factors, and the constant one
survive the temporary bank. Only four persistent working arrays change.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def exponentTemps (n : Nat) : List (Nat × Nat) := [(kOk, 44), (hdr, 15 * S n)]
def exponentArrays : List Nat := [aD, aDen, aU, aV]
def exponentRanges (n : Nat) : List (Nat × Nat) := exponentTemps n ++ ranges n exponentArrays []

theorem exponent_temps_keep {m m' : Mem} {B : Addr} {k n : Nat} {js ds : List Nat}
    (width : k ≤ n) (arrays : ∀ j ∈ js, j < 15)
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 44) (O : Keep B k js ds m m') :
    Outs B (exponentTemps n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentTemps], ?_, ?_⟩
    · unfold arr
      omega
    · have endK := arr_end (w := k) (arrays j hj)
      have growth : arr k 15 ≤ arr n 15 := by unfold arr S; omega
      have E : arr n 15 = hdr + 15 * S n := rfl
      rw [E] at growth
      omega
  · exact ⟨(kOk, 44), by simp [exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

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
  all_goals exact ⟨(kOk, 44), by simp [exponentTemps], by decide, by decide⟩

theorem exponent_temps_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (exponentTemps n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have lower : hdr ≤ arr n j := Nat.le_add_right ..
    exact Or.inr (Nat.le_trans (by decide : kOk + 44 ≤ hdr) lower)
  · exact Or.inr (arr_mono persistent)

theorem exponent_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (unchanged : ∀ a ∈ exponentArrays, j ≠ a)
    (fit : arr n j + S n ≤ 2 ^ 64) (O : Outs B (exponentRanges n) m m') :
    num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · have lower : hdr ≤ arr n j := Nat.le_add_right ..
      exact Or.inr (Nat.le_trans (by decide : kOk + 44 ≤ hdr) lower)
    · exact Or.inr (arr_mono persistent)
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨a, ha, rfl⟩ := output
    have D := arr_disj (w := n) (unchanged a ha)
    simp only at D ⊢
    unfold S at D ⊢
    omega

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
