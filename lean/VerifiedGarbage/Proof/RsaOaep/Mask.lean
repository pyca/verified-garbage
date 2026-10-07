import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Spec.RsaOaep

/-!
# RSAES-OAEP: masking and unmasking `EM`, whatever the target

An implementation's working space as a function from offsets to bytes
(`V`), with the first `n` bytes of a mask XORed in from offset `e`
(`mixV`): `EM = 0x00 ‖ seed ‖ DB` (from offset 0) masked as an
implementation does it (`DB` with MGF1 of the seed, then the seed with MGF1
of the masked `DB`) is EME-OAEP's encoding (`em_mask`), and `EM` unmasked in
place (the seed with MGF1 of `maskedDB`, then `maskedDB` with MGF1 of the
seed) gives the seed and `DB` that `decode` computes (`unmask`).
-/

namespace VG.Proof.RsaOaep

open VG
open VG.Spec.Mgf1 (Hash xorBytes mgf1)
open VG.Proof.Mgf1 (Valid xorBytes_getD mgf1_length getD_append ifp ifn)

/-- `dst` with the first `n` bytes of the mask `mk` XORed in. -/
def mixV (V : Nat → Byte) (mk : List Byte) (e n : Nat) (o : Nat) : Byte :=
  if e ≤ o ∧ o < e + n then V o ^^^ mk.getD (o - e) 0 else V o

theorem map_range_getD {f : Nat → Byte} {n : Nat} {xs : List Byte} (h : (List.range n).map f = xs) {j : Nat}
    (hj : j < n) : f j = xs.getD j 0 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- The bytes of `src`, as `V` has them. -/
def srcB (V : Nat → Byte) (src srcLen : Nat) : List Byte := (List.range srcLen).map fun i => V (src + i)

theorem range_ext {f : Nat → Byte} {xs : List Byte} {n : Nat} (hl : xs.length = n)
    (h : ∀ i < n, f i = xs.getD i 0) : (List.range n).map f = xs := by
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range]
  rw [h i (by simpa using h₁), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  rfl

theorem srcB_eq {V : Nat → Byte} {src n : Nat} {xs : List Byte} (hl : xs.length = n)
    (h : ∀ i < n, V (src + i) = xs.getD i 0) : srcB V src n = xs := range_ext hl h

/-- The masking of `EM = 0x00 ‖ seed ‖ DB` (`V₁`): `DB` with MGF1 of the seed,
then the seed with MGF1 of the masked `DB`. -/
theorem em_mask {G : Hash} (hG : Valid G) {V₁ : Nat → Byte} {D k : Nat} {sd db : List Byte} (hk : D + 1 ≤ k)
    (hsd : sd.length = D) (hdb : db.length = k - D - 1) (h0 : V₁ 0 = 0) (hs : ∀ i < D, V₁ (1 + i) = sd.getD i 0)
    (hd : ∀ i < k - D - 1, V₁ (1 + D + i) = db.getD i 0) :
    (List.range k).map (fun i => mixV (mixV V₁ (mgf1 G (srcB V₁ 1 D) (k - D - 1)) (1 + D) (k - D - 1))
      (mgf1 G (srcB (mixV V₁ (mgf1 G (srcB V₁ 1 D) (k - D - 1)) (1 + D) (k - D - 1)) (1 + D) (k - D - 1)) D) 1 D i) =
      0 :: xorBytes sd (mgf1 G (xorBytes db (mgf1 G sd (k - D - 1))) D) ++ xorBytes db (mgf1 G sd (k - D - 1)) := by
  have e1 : srcB V₁ 1 D = sd := srcB_eq hsd hs
  have hm1 := mgf1_length hG sd (k - D - 1)
  have hmdb : (xorBytes db (mgf1 G sd (k - D - 1))).length = k - D - 1 := by
    rw [Proof.Mgf1.xorBytes_length, hdb, hm1, Nat.min_self]
  have e2 : srcB (mixV V₁ (mgf1 G sd (k - D - 1)) (1 + D) (k - D - 1)) (1 + D) (k - D - 1) =
      xorBytes db (mgf1 G sd (k - D - 1)) := by
    refine srcB_eq hmdb fun i hi => ?_
    rw [mixV, ifp (by omega), Nat.add_sub_cancel_left, hd i hi,
      xorBytes_getD (by omega) (by omega)]
  rw [e1, e2]
  have hm2 := mgf1_length hG (xorBytes db (mgf1 G sd (k - D - 1))) D
  have hms : (xorBytes sd (mgf1 G (xorBytes db (mgf1 G sd (k - D - 1))) D)).length = D := by
    rw [Proof.Mgf1.xorBytes_length, hsd, hm2, Nat.min_self]
  refine range_ext (by simp only [List.length_cons, List.length_append, hms, hmdb]; omega) fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp only [mixV]; rw [ifn (by omega), ifn (by omega), h0]; rfl
  rw [show (0 :: xorBytes sd (mgf1 G (xorBytes db (mgf1 G sd (k - D - 1))) D) ++
      xorBytes db (mgf1 G sd (k - D - 1))).getD i 0 =
      (xorBytes sd (mgf1 G (xorBytes db (mgf1 G sd (k - D - 1))) D) ++
        xorBytes db (mgf1 G sd (k - D - 1))).getD (i - 1) 0 by
    cases i with
    | zero => omega
    | succ j => simp [List.getD_eq_getElem?_getD]]
  rw [getD_append, hms]
  by_cases h1 : i - 1 < D
  · rw [ifp h1, mixV, ifp (by omega), mixV, ifn (by omega),
      xorBytes_getD (by omega) (by omega), show i - 1 = i - 1 from rfl]
    rw [show i = 1 + (i - 1) by omega, hs _ h1, Nat.add_sub_cancel_left]
  · rw [ifn h1, mixV, ifn (by omega), mixV, ifp (by omega)]
    rw [xorBytes_getD (by omega) (by omega)]
    rw [show i = 1 + D + (i - 1 - D) by omega, hd _ (by omega)]
    congr 2 <;> omega

theorem map_range_getD' (V : Nat → Byte) {k i : Nat} (hi : i < k) : ((List.range k).map V).getD i 0 = V i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem drop_getD' (l : List Byte) (n i : Nat) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem take_getD' (l : List Byte) {n i : Nat} (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The seed and `DB`, unmasked from `EM` (`k` bytes of `V`). -/
theorem unmask {G : Hash} (hG : Valid G) (V : Nat → Byte) {D k : Nat} (hk : 2 * D + 2 ≤ k) :
    srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D =
      xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D) ∧
    srcB (mixV (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D)
        (mgf1 G (srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1)) (1 + D) (k - D - 1))
        (1 + D) (k - D - 1) =
      xorBytes (((List.range k).map V).drop (D + 1))
        (mgf1 G (xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D))
          (k - D - 1)) := by
  have hlen : ((List.range k).map V).length = k := by simp
  have e1 : srcB V (1 + D) (k - D - 1) = ((List.range k).map V).drop (D + 1) := by
    refine srcB_eq (by simp; omega) fun i hi => ?_
    rw [drop_getD', map_range_getD' V (by omega)]; congr 1; omega
  have hms : ((((List.range k).map V).drop 1).take D).length = D := by simp; omega
  have hm1 := mgf1_length hG (((List.range k).map V).drop (D + 1)) D
  have hseedl : (xorBytes ((((List.range k).map V).drop 1).take D)
      (mgf1 G (((List.range k).map V).drop (D + 1)) D)).length = D := by
    rw [Proof.Mgf1.xorBytes_length, hms, hm1, Nat.min_self]
  have e2 : srcB (mixV V (mgf1 G (srcB V (1 + D) (k - D - 1)) D) 1 D) 1 D =
      xorBytes ((((List.range k).map V).drop 1).take D) (mgf1 G (((List.range k).map V).drop (D + 1)) D) := by
    refine srcB_eq hseedl fun i hi => ?_
    rw [mixV, ifp (by omega), e1, xorBytes_getD (by omega) (by omega), take_getD' _ hi, drop_getD',
      map_range_getD' V (by omega), Nat.add_sub_cancel_left]
  refine ⟨e2, ?_⟩
  rw [e2]
  have hmdb : (((List.range k).map V).drop (D + 1)).length = k - D - 1 := by simp; omega
  refine srcB_eq (by rw [Proof.Mgf1.xorBytes_length, hmdb, mgf1_length hG, Nat.min_self]) fun i hi => ?_
  rw [mixV, ifp (by omega), mixV, ifn (by omega), xorBytes_getD (by omega) (by rw [mgf1_length hG]; omega),
    drop_getD', map_range_getD' V (by omega), Nat.add_sub_cancel_left]
  congr 2; omega

theorem range_map_getD {xs : List Byte} {n : Nat} (h : n ≤ xs.length) :
    (List.range n).map (fun i => xs.getD i 0) = xs.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp at h₁; omega)]
  rfl

end VG.Proof.RsaOaep
