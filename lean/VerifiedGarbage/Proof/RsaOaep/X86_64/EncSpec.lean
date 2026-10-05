import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Spec.RsaOaep

/-!
# RSAES-OAEP encryption on x86-64: the encoding the code computes

`EM`'s bytes before masking, `0x00 ‖ seed ‖ DB`, masked as the code does it
(`DB` with MGF1 of the seed, then the seed with MGF1 of the masked `DB`,
each a `mixV`), are EME-OAEP's encoding (`em_mask`, `encode_eq`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG
open VG.Spec.Mgf1 (Hash xorBytes mgf1)
open VG.Proof.MlKem.X86_64 (ifp ifn)
open VG.Proof.Mgf1 (Valid xorBytes_getD mgf1_length getD_append)

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

end VG.Proof.RsaOaep.X86_64
