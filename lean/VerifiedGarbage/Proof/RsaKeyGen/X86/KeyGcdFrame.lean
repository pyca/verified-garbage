module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrom
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge

/-! # The native GCD stage keeps the primes and totient product intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def gcdPartArrays : List Nat := [aT1, aT2, aU, aV, aDen]
def gcdPartRanges (n k : Nat) : List (Nat × Nat) :=
  gcdRanges n k ++ ranges n gcdPartArrays [kFlag]

theorem gcdPart_preserves_num {m m' : Mem} {B : Addr} {n k j : Nat}
    (width : k ≤ n) (persistent : 15 ≤ j) (ju : j ≠ aU) (jv : j ≠ aV) (jd : j ≠ aDen)
    (fit : arr n j + S n ≤ 2 ^ 64) (changed : Outs B (gcdPartRanges n k) m m') :
    num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply changed.val32 _ (by unfold S at fit; omega)
  intro r hr
  change r ∈ gcdRanges n k ++ ranges n gcdPartArrays [kFlag] at hr
  rcases List.mem_append.mp hr with inv | other
  · change r ∈ inverseRanges k invSlots ++ [(arr n aDen, S n)] at inv
    rcases List.mem_append.mp inv with small | den
    · simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at small
      rcases small with rfl | rfl | rfl | rfl
      · have endBound := inverse_end_le width persistent
        have endEq : arr k 15 = hdr + 4 * (15 * (k + 2)) := by unfold arr S; omega
        rw [endEq] at endBound
        exact Or.inr endBound
      all_goals have lower : hdr ≤ arr n j := Nat.le_add_right ..
      all_goals simp only [sOdd, sB, sC, hdr] at lower ⊢
      all_goals omega
    · simp only [List.mem_singleton] at den
      subst r
      have D := arr_disj (w := n) jd
      simp only at D ⊢
      unfold S at D ⊢
      omega
  · simp only [ranges, List.mem_append, List.mem_map] at other
    rcases other with ⟨a, ha, rfl⟩ | ⟨d, hd, rfl⟩
    · have different : j ≠ a := by
        simp only [gcdPartArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl
        · unfold aT1
          omega
        · unfold aT2
          omega
        · exact ju
        · exact jv
        · exact jd
      have D := arr_disj (w := n) different
      simp only at D ⊢
      unfold S at D ⊢
      omega
    · simp only [List.mem_singleton] at hd
      subst d
      have lower : hdr ≤ arr n j := Nat.le_add_right ..
      exact Or.inr (Nat.le_trans (by decide : kFlag + 4 ≤ hdr) lower)

end VG.Proof.RsaKeyGen.X86.Key
