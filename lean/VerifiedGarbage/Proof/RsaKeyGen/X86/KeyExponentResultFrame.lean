module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrection
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDProduct
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # Result arithmetic preserves the already-computed inverse status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def exponentResultRanges (n : Nat) : List (Nat × Nat) :=
  (kProduct, 4) :: (hdr, 15 * S n) :: ranges n exponentArrays []

theorem exponent_result_frame {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (exponentResultRanges n) m m') : Outs B (exponentRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact ⟨(kOk, 68), by simp [exponentRanges, exponentTemps], by decide, by decide⟩
  · exact ⟨(hdr, 15 * S n), by simp [exponentRanges, exponentTemps], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨r, List.mem_append_right _ array, Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_header {m m' : Mem} {B : Addr} {n d count : Nat}
    (bound : d + 4 * count ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    val32 m' B d count = val32 m B d count := by
  apply O.val32 _ (by unfold kProduct at bound; omega)
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact Or.inl bound
  · exact Or.inl (Nat.le_trans bound (by decide : kProduct ≤ hdr))
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at array
    obtain ⟨a, _, rfl⟩ := array
    have lower : hdr ≤ arr n a := Nat.le_add_right ..
    exact Or.inl (Nat.le_trans bound (Nat.le_trans (by decide : kProduct ≤ hdr) lower))

theorem exponent_result_slot {m m' : Mem} {B : Addr} {n d : Nat}
    (bound : d + 4 ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    slot m' B d = slot m B d := by
  have H := exponent_result_header (count := 1) bound O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem exponent_result_complement {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outside B (arr n aDen) (S n) m m') : Outs B (exponentResultRanges n) m m' :=
  Outs.of_outside O (by simp [exponentResultRanges, ranges, exponentArrays])

theorem correction_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (unchanged : j ≠ aV) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (correctionRanges n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · have lower : hdr ≤ arr n j := Nat.le_add_right ..
    exact Or.inr (Nat.le_trans (by decide : kProduct + 4 ≤ hdr) lower)
  · have lower : 256 ≤ arr n 15 :=
      Nat.le_trans (by decide : 256 ≤ 160 + 15 * (4 * 2))
        (Nat.add_le_add_left (Nat.mul_le_mul_left 15 (Nat.mul_le_mul_left 4 (Nat.le_add_left 2 n))) 160)
    exact Or.inr (Nat.le_trans lower (arr_mono persistent))
  · have D := arr_disj (w := n) unchanged
    simp only at D ⊢
    unfold S at D ⊢
    omega

theorem exponent_result_correction {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (correctionRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨(kProduct, 4), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], Nat.le_refl _, ?_⟩
    unfold S
    omega
  · exact ⟨(arr n aV, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_product {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (dProductRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [dProductRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨(kProduct, 4), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], ?_, ?_⟩
    · unfold arr
      omega
    · unfold arr S
      omega
  · exact ⟨(arr n aD, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, by unfold S; omega⟩

end VG.Proof.RsaKeyGen.X86.Key
