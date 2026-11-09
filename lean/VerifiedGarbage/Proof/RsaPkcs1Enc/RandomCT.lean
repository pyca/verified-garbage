module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random

/-!
# Drawing the padding string: what two runs with the same trace share

Two tapes whose scans have the same trace (`padSearch`'s, which the contract
makes public) keep as many octets as each other after each octet the scan
reads (`nz_take_length_eq`), and the scan stops after the same octet
(`stop_iff`), so every count and branch of an implementation's scan is the
same in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec.RsaPkcs1Enc

theorem nz_take_succ {r : List Byte} {j : Nat} (hj : j < r.length) :
    (nz (r.take (j + 1))).length = (nz (r.take j)).length + if r.getD j 0 = 0 then 0 else 1 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, nz_append]
  have e : r.getD j 0 = r[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e]
  by_cases h : r[j] = 0
  · rw [h]; simp [nz]
  · rw [show nz [r[j]] = [r[j]] from by rw [show [r[j]] = [] ++ [r[j]] from rfl, nz_ne h, nz_nil]]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [ite_eq_right h]

/-- With the same trace, as many octets kept after each octet the scan reads. -/
theorem nz_take_length_eq {n : Nat} {r₁ r₂ : List Byte}
    (h : (padSearch n r₁).trace = (padSearch n r₂).trace) :
    ∀ j, j ≤ scanLen n r₁ → (nz (r₁.take j)).length = (nz (r₂.take j)).length
  | 0, _ => by simp [nz_nil]
  | j + 1, hj => by
    have hs := scanLen_eq h
    have h1 := scanLen_le n r₁
    have h2 := scanLen_le n r₂
    rw [nz_take_succ (by omega), nz_take_succ (by omega), nz_take_length_eq h j (by omega)]
    have hz := zero_iff (i := j) h (by omega)
    by_cases h0 : r₁.getD j 0 = 0
    · rw [ite_eq_left h0, ite_eq_left (hz.mp h0)]
    · rw [ite_eq_right h0, ite_eq_right (fun h' => h0 (hz.mpr h'))]

/-- Within the scan, after octet `j`: it stops there exactly when it has
kept `n` octets or read the whole tape. -/
theorem stop_iff {n : Nat} {r : List Byte} {j : Nat} (hj : j < scanLen n r)
    (hc : (nz (r.take j)).length < n) :
    ((nz (r.take (j + 1))).length = n ∨ j + 1 = r.length) ↔ scanLen n r = j + 1 := by
  have hl := scanLen_le n r
  constructor
  · rintro (h | h)
    · -- the octet `j` is the `n`th nonzero one
      have hz : r.getD j 0 ≠ 0 := by
        intro h0; rw [nz_take_succ (by omega), ite_eq_left h0] at h; omega
      have e : r = r.take j ++ r.getD j 0 :: r.drop (j + 1) := by
        conv => lhs; rw [← List.take_append_drop j r]
        congr 1
        rw [List.drop_eq_getElem_cons (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < r.length by omega)]
      rw [nz_take_succ (by omega), ite_eq_right hz] at h
      rw [e, scanLen_last _ hz (by omega), List.length_take, Nat.min_eq_left (by omega)]
    · have := lt_scanLen (n := n) (i := j) hc (by omega)
      omega
  · intro h
    by_cases hf : (nz (r.take (j + 1))).length < n
    · right
      by_cases hne : j + 1 = r.length
      · exact hne
      · have := lt_scanLen (n := n) (i := j + 1) hf (by omega)
        omega
    · left
      have := nz_take_succ (r := r) (j := j) (by omega)
      split at this <;> omega

end VG.Proof.RsaPkcs1Enc
