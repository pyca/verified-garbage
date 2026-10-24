module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Post
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on PPC64LE: the checks are EMSA-PSS-VERIFY's

Untrusted: everything here is checked by Lean. For `EM` of `emLen = E`
bytes after `lo` (`lN`) in the view `V`, `DB` unmasked as the code does
(`wR`) is `Proof.RsaPss.vDb` (`wR_eq`), and `Res` (`Post.lean`) holds
exactly when the leading byte is zero if `lo = 1` and the encoding is
consistent byte by byte (`Proof.RsaPss.EncOk`, `res_iff`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG
open VG.Proof.RsaPss (lz vDb vH EncOk)
open VG.Proof.RsaPss (xorBytes_getD clearTop_getD zeros_getD eq_range_map)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn Valid mgf1_length xorBytes_length)
open VG.Spec.RsaPss (zeros clearTop)

section
variable {Gs : Spec.Mgf1.Hash} {V : Nat → Byte} {em : List Byte} {lN E : Nat} {c : Byte} {z : Nat}

theorem vH_getD (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) {i : Nat} (hi : i < Gs.len) :
    (vH Gs em (E - Gs.len - 1)).getD i 0 = V (lN + (E - Gs.len - 1) + i) := by
  simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD, Nat.add_assoc, hV _ (by omega_arith)]

theorem vH_length (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) : (vH Gs em (E - Gs.len - 1)).length = Gs.len := by
  simp only [vH, List.length_take, List.length_drop, hE]; omega_arith

theorem srcB_vH (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) :
    srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len = vH Gs em (E - Gs.len - 1) := by
  refine (eq_range_map (vH_length hE hfE) fun i hi => ?_).symm
  rw [vH_getD hfE hV hi, v1, ifn (by omega_arith)]

theorem wR_eq (hGv : Valid Gs) (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
    (hV : ∀ i < E, V (lN + i) = em.getD i 0) {j : Nat} (hj : j < E - Gs.len - 1) :
    wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) j = (vDb Gs em (E - Gs.len - 1) z).getD j 0 := by
  have hmk := mgf1_length hGv (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have ht : ∀ {i}, i < E - Gs.len - 1 → (em.take (E - Gs.len - 1)).getD i 0 = em.getD i 0 := fun hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi]
  let mk := Spec.Mgf1.mgf1 Gs (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have hm : mixV (v1 V lN c (lN + E)) (Spec.Mgf1.mgf1 Gs (srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len)
      (E - Gs.len - 1)) lN (E - Gs.len - 1) (lN + j) = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [srcB_vH hE hfE hV, mixV, ifp ⟨by omega_arith, by omega_arith⟩, v1, ifn (by omega_arith), hV _ (by omega_arith),
      Nat.add_sub_cancel_left]
  have hx : (Spec.Mgf1.xorBytes (em.take (E - Gs.len - 1)) mk).getD j 0 = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [xorBytes_getD (by rw [List.length_take, hE]; omega_arith) (by simp only [mk]; omega_arith), ht hj]
  show (if lN + j = lN then _ &&& c else _) = _
  rw [vDb, clearTop_getD]
  by_cases e : j = 0
  · subst e
    rw [ifp (Nat.add_zero lN), ifp rfl, hm, ← hx, hc]
  · rw [ifn (by omega_arith), ifn e, hm, ← hx]

end

section
variable {Gs : Spec.Mgf1.Hash} (hGv : Valid Gs) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0)

include hGv hc hE hfE hV in
theorem db_eq : vDb Gs em (E - Gs.len - 1) z = (List.range (E - Gs.len - 1)).map (wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) := by
  refine eq_range_map (by simp [vDb, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega_arith)
    fun j hj => (wR_eq hGv hc hE hfE hV hj).symm

include hGv hc hE hfE hV in
theorem lzr_eq : lzr (wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) (E - Gs.len - 1) = lz (vDb Gs em (E - Gs.len - 1) z) := by
  rw [db_eq hGv hc hE hfE hV]; rfl

include hGv hc hE hfE hV in
/-- `M'` is the specification's once the delimiter is found and the salt
length is the expected one. -/
theorem mR_eq (hmh : mh.length = Gs.len) {any saltLen : BitVec 64}
    (hlz : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1)
    (hsl : any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z)) :
    mR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen =
      zeros 8 ++ mh ++ (vDb Gs em (E - Gs.len - 1) z).drop (lz (vDb Gs em (E - Gs.len - 1) z) + 1) := by
  have hl := lzr_eq hGv hc hE hfE hV
  generalize hdb : vDb Gs em (E - Gs.len - 1) z = db at hl hlz hsl
  have hdl : db.length = E - Gs.len - 1 := by
    rw [← hdb]; simp [vDb, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega
  have hp : posR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = lz db := by rw [posR, hl, ifp hlz]
  have hw : ∀ j < E - Gs.len - 1, dbV Gs (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + j) = db.getD j 0 :=
    fun j hj => by rw [← hdb, ← wR_eq hGv hc hE hfE hV hj]; rfl
  have hd : ∀ j < E - Gs.len - 1 - lz db - 1, (db.drop (lz db + 1)).getD j 0 =
      dbV Gs (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + (j + (lz db + 1))) := fun j hj => by
    rw [hw _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  have hdd : (db.drop (lz db + 1)).length = E - Gs.len - 1 - lz db - 1 := by rw [List.length_drop, hdl]; omega
  rw [mR]
  split
  · rename_i h0
    have h1 := hsl h0
    rw [mFix, h1, show E - Gs.len - 1 - 1 - lz db = E - Gs.len - 1 - lz db - 1 by omega]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega)]; congr 1; omega
  · rw [mAny, hp, slR, hp]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega), ifp (by omega)]

end

theorem setWidth64_eq_zero (a : Byte) : a.setWidth 64 = 0#64 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

theorem setWidth64_xor1 (a : Byte) : (a.setWidth 64 ^^^ 1#64) = 0#64 ↔ a = 1 := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

section
variable {Gs : Spec.Mgf1.Hash} (hGv : Valid Gs) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0) (hmh : mh.length = Gs.len)
include hGv hc hE hfE hV hmh

theorem res_iff {any saltLen : BitVec 64} {sLen : Option Nat} (hs : sLen = if any = 0 then some saltLen.toNat else none)
    (hE64 : E < 2 ^ 64) :
    Res Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen ↔
      (lN = 1 → V 0 = 0) ∧ EncOk Gs mh em E z sLen := by
  have hl := lzr_eq hGv hc hE hfE hV
  have hw : ∀ j < E - Gs.len - 1, wR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) j =
      (vDb Gs em (E - Gs.len - 1) z).getD j 0 := fun j hj => wR_eq hGv hc hE hfE hV hj
  have hk1 : lN + E - 1 = lN + (E - 1) := by omega_arith
  have hV0 : V lN = em.getD 0 0 := hV 0 (by omega_arith)
  have hVk : V (lN + E - 1) = em.getD (E - 1) 0 := by rw [hk1]; exact hV _ (by omega_arith)
  have hnot : ~~~c = ~~~((0xFF : Byte) >>> z) := by rw [hc]
  -- The hash compared, as lists.
  have hcmp : ∀ M : List Byte, (∀ i < Gs.len, V (lN + (E - Gs.len - 1) + i) = (Gs.hash M).getD i 0) ↔
      Gs.hash M = vH Gs em (E - Gs.len - 1) := fun M => by
    constructor
    · intro h
      refine List.ext_getElem (by rw [hGv.2, vH_length hE hfE]) fun i h₁ h₂ => ?_
      have e := h i (by rw [hGv.2] at h₁; exact h₁)
      rw [← vH_getD hfE hV (by rw [hGv.2] at h₁; exact h₁), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at e
      exact e.symm
    · intro h i hi; rw [h, vH_getD hfE hV hi]
  have hval : valR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = 1 ↔
      lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 ∧
        (vDb Gs em (E - Gs.len - 1) z).getD (lz (vDb Gs em (E - Gs.len - 1) z)) 0 = 1 := by
    unfold valR; rw [hl]
    by_cases h : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1
    · rw [ifp h, hw _ h]; simp [h]
    · rw [ifn h]; simp [h]
  have hsl : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      slR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z) :=
    fun h => by unfold slR posR; rw [hl, ifp h]; omega_arith
  have hsv : (sLen = none ∨ sLen = some (E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z))) ↔
      (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z)) := by
    rw [hs]; split
    · rename_i h0; simp [h0]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => Or.inl rfl⟩
  have hany : lz (vDb Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      ((if any = 0 then BitVec.ofNat 64 (slR Gs V Gs.len lN (E - Gs.len - 1) c (lN + E)) ^^^ saltLen else 0#64) =
        0#64 ↔ (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb Gs em (E - Gs.len - 1) z))) := fun h => by
    rw [hsl h]
    split
    · rename_i h0
      rw [BitVec.xor_eq_zero_iff]
      constructor
      · intro e _; rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      · intro e; rw [← e h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => rfl⟩
  unfold Res accR accW EncOk
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, setWidth64_eq_zero, accB_eq_zero, setWidth64_xor1, hVk, hV0, hnot]
  constructor
  · rintro ⟨⟨⟨⟨ha1, ha2, ha3⟩, hv⟩, hy⟩, hh⟩
    obtain ⟨hlz, h1⟩ := hval.mp hv
    have hy' := (hany hlz).mp hy
    refine ⟨ha3, ha1, ha2, hlz, h1, hsv.mpr hy', ?_⟩
    rw [← mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mp hh
  · rintro ⟨ha3, ha1, ha2, hlz, h1, hy, hh⟩
    have hy' := hsv.mp hy
    refine ⟨⟨⟨⟨ha1, ha2, ha3⟩, hval.mpr ⟨hlz, h1⟩⟩, (hany hlz).mpr hy'⟩, ?_⟩
    rw [mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mpr hh
end

end VG.Proof.RsaPss.PPC64LE
