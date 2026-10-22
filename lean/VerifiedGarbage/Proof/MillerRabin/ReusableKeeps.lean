module

public import VerifiedGarbage.Proof.MillerRabin.Reusable
public import VerifiedGarbage.Proof.MillerRabin.Workspace
import VerifiedGarbage.Proof.Framework.Offset

/-! The shared round contract retains all data needed by the next witness. -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Spec.Rsa.Mont

theorem kept_layout {m m' : Mem} {B : Addr} {len : Nat}
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact m B len)
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B len (wOf m B) m m') :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact m' B len ∧ wOf m' B = wOf m B := by
  have fit : arrAt (wOf m B) 28 ≤ 8 * len := L.2.2.2.2.1
  have headerFit : 32 ≤ len := by
    have : 256 ≤ arrAt (wOf m B) 28 := Nat.le_add_right _ _
    omega
  apply Workspace.compact_layout_header_congr ?_ ?_ ?_ L
  · exact kept_header K headerFit (by decide : 6 < 32) (by decide)
  · intro j hj
    exact kept_header K headerFit (by unfold arrWord; omega) (by
      simp only [arrWord, List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega)
  · exact kept_header K headerFit (by decide : 28 < 32) (by decide)

private theorem tail_fit {w len : Nat} (fit : arrAt w 28 ≤ 8 * len) :
    arrAt w 27 + 8 * w + 8 ≤ 8 * len := by
  calc
    arrAt w 27 + 8 * w + 8 ≤ arrAt w 27 + 8 * (w + 2) := by omega
    _ = arrAt w 28 := by
      change hdrBytes + 27 * (8 * (w + 2)) + 8 * (w + 2) = hdrBytes + (27 + 1) * (8 * (w + 2))
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    _ ≤ 8 * len := fit

theorem kept_candidate_low {m m' : Mem} {B : Addr} {len w : Nat}
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B len w m m')
    (positive : 0 < w) (fit : arrAt w 28 ≤ 8 * len) :
    m'.readW (B + BitVec.ofNat 64 (arrAt w 0)) 64 =
      m.readW (B + BitVec.ofNat 64 (arrAt w 0)) 64 := by
  apply keeps_word K
  · have chunk : 8 ≤ 8 * (w + 2) := by omega
    have scale : 8 * (w + 2) ≤ 28 * (8 * (w + 2)) := Nat.le_mul_of_pos_left _ (by decide)
    have bound : arrAt w 0 + 8 ≤ arrAt w 28 := by
      simpa only [arrAt, Nat.zero_mul, Nat.add_zero] using
        Nat.add_le_add_left (Nat.le_trans chunk scale) hdrBytes
    exact Nat.le_trans bound fit
  · intro k hk
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      right <;> simp only [arrAt, hdrBytes] <;> omega
  · intro j hj
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      left <;> simp only [arrAt, hdrBytes] <;> omega
  · left; simp only [Spec.MillerRabin.compact, arrAt, hdrBytes]; omega

theorem kept_exponent_tail {m m' : Mem} {B : Addr} {len w : Nat}
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B len w m m')
    (fit : arrAt w 28 ≤ 8 * len) :
    m'.readW (B + BitVec.ofNat 64 (arrAt w 27 + 8 * w)) 64 =
      m.readW (B + BitVec.ofNat 64 (arrAt w 27 + 8 * w)) 64 := by
  apply keeps_word K
  · exact tail_fit fit
  · intro k hk
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      right <;> simp only [arrAt, hdrBytes] <;> omega
  · intro j hj
    simp only [Spec.MillerRabin.compact, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      right <;> simp only [arrAt, hdrBytes] <;> omega
  · right
    change arrAt w 27 ≤ arrAt w 27 + 8 * w
    exact Nat.le_add_right _ _

theorem PreparedCore.kept {m m' : Mem} {B : Addr} {len : Nat} (P : PreparedCore m B)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact m B len)
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B len (wOf m B) m m') :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact m' B len ∧ PreparedCore m' B := by
  obtain ⟨Lt, W⟩ := kept_layout L K
  have fit : arrAt (wOf m B) 28 ≤ 8 * len := L.2.2.2.2.1
  have headerFit : 32 ≤ len := by
    have : 256 ≤ arrAt (wOf m B) 28 := Nat.le_add_right _ _
    omega
  have inverse := kept_header K headerFit (by decide : 7 < 32) (by decide)
  change wordAt m' B minvWord = wordAt m B minvWord at inverse
  have candidate := kept_number K fit (j := 0) (.inl rfl)
  have one := kept_number K fit (j := 9) (.inr (.inl rfl))
  have minus := kept_number K fit (j := 10) (.inr (.inr (.inl rfl)))
  have exponent := kept_number K fit (j := 27) (.inr (.inr (.inr rfl)))
  refine ⟨Lt, ?_⟩
  constructor
  · rw [W, candidate]; exact P.large
  · rw [W, candidate]; exact P.odd
  · rw [W, kept_candidate_low K (by have := L.2.2.1; omega) fit, inverse]; exact P.inverse
  · rw [W, candidate, one]; exact P.one
  · rw [W, candidate, minus]; exact P.minus
  · rw [W, candidate, exponent]; exact P.exponent
  · rw [W, candidate, kept_exponent_tail K fit]; exact P.tail

end VG.Proof.MillerRabin
