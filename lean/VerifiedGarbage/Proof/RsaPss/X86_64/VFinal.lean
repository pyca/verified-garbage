module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VLogic
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS verification on x86-64: the result

`vfinal`: from `EM` (RSAVP1's result or zeros) at `scratch + oEm` and `DB`
unmasked and its top bits cleared, the accumulator and the salt's hash that
`verifyMain` computes are zero and `H` exactly when `Spec.RsaPss.verify`
holds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64
open VG.Impl.RsaOaep.X86_64 (oEm oSt)
open VG.Proof.RsaOaep.X86_64 (upd)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaPss (lz)
open VG.Proof.MlKem.X86_64 (ifp ifn)

theorem range_take_drop {g : Nat → Byte} {x : List Byte} {a n : Nat} (hx : a + n ≤ x.length)
    (h : ∀ i < n, g i = x.getD (a + i) 0) : (List.range n).map g = (x.drop a).take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [h i h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

theorem getD_take_drop {x : List Byte} {a n i : Nat} (hi : i < n) :
    ((x.drop a).take n).getD i 0 = x.getD (a + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]

theorem setWidth_ofNat8 (a : Nat) : (BitVec.ofNat 64 a).setWidth 8 = BitVec.ofNat 8 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem getD_map_range' {f : Nat → Byte} {n k : Nat} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]

/-- `DB` after the mask and the top bits. -/
theorem db_bytes (V : Nat → Byte) (mk : List Byte) {e db z : Nat} (hmk : mk.length = db) :
    ∀ i < db, upd (mixV V mk e db) e (mixV V mk e db e &&& ((0xFF : Byte) >>> z)) (e + i) =
      (Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk)).getD i 0 := by
  intro i hi
  rw [VG.Proof.RsaPss.clearTop_getD]
  have hx : ∀ j < db, (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk).getD j 0 =
      V (e + j) ^^^ mk.getD j 0 := fun j hj => by
    rw [VG.Proof.RsaPss.xorBytes_getD (by simp; omega) (by omega), getD_map_range' hj]
  simp only [upd, mixV]
  by_cases h0 : i = 0
  · subst h0
    rw [ifp (by omega), ifp rfl, ifp (show e ≤ e ∧ e < e + db by omega), hx 0 hi, Nat.sub_self, Nat.add_zero]
  · rw [ifn (by omega), ifn h0, ifp (show e ≤ e + i ∧ e + i < e + db by omega), hx i hi,
      show e + i - e = i by omega]

theorem fnz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → fnz f j = fnz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [fnz, fnz_congr (j := j) (fun i hi => h i (by omega)), h j (by omega)]

/-- The mask `verifyMain` uses, `0xFF >>> z`. -/
theorem maskV_eq {n₀ : Byte} (rest : List Byte) (h0 : n₀ ≠ 0) :
    (maskV n₀.toNat).setWidth 8 = (0xFF : Byte) >>> (8 * Spec.RsaPss.emLength
      (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) - (Spec.RsaPss.bitLength
        (Spec.Rsa.os2ip (n₀ :: rest)) - 1)) := by
  rw [VG.Proof.RsaPss.mask_eq rest h0, maskV]
  split
  · rfl
  · exact setWidth_ofNat8 _

/-- `DB` as `verifyMain` leaves it, from its start `e`: the bytes `V6`, the
first ANDed with the mask `c`. -/
def vfz (V6 : Nat → Byte) (c : Byte) (e : Nat) : Nat → Byte := fun i => upd V6 e (V6 e &&& c) (e + i)

theorem vfinal {Hh Gh : Spec.Mgf1.Hash} (hHv : Proof.Mgf1.Valid Hh) (hGv : Proof.Mgf1.Valid Gh)
    {n₀ : Byte} {rest eB sB mHash : List Byte} {D lo db : Nat} {fixed : Bool} {slen : BitVec 64}
    {V3 V6 : Nat → Byte}
    (h0 : n₀ ≠ 0) (hk1 : 64 ≤ rest.length + 1) (hk2 : rest.length + 1 ≤ 1024)
    (hlo : lo = loV n₀.toNat) (hsB : sB.length = rest.length + 1) (hmH : mHash.length = Hh.len) (hD : Hh.len = D)
    (hdb : rest.length + 1 - lo - (D + 2) + 1 = db)
    (hfit : D + 2 + (if fixed then slen.toNat else 0) ≤ rest.length + 1 - lo)
    (hV3 : ∀ i < rest.length + 1, V3 (oEm + i) = ((Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD
      (Spec.RsaPss.zeros (rest.length + 1))).getD i 0)
    (hV6 : ∀ o < oSt, V6 o = mixV V3 (Spec.Mgf1.mgf1 Gh (srcB V3 (oEm + lo + db) D) db) (oEm + lo) db o) :
    (acc1V (acc0V (V3 (oEm + (rest.length + 1) - 1)) (V3 oEm) (V3 (oEm + lo)) ((maskV n₀.toNat).setWidth 8) lo)
        (fnz (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)) db).isSome
        (((fnz (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)) db).map
          (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo))).getD 0) fixed
        (BitVec.ofNat 64 (db - (fnz (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)) db).getD 0 - 1)) slen = 0 ∧
      ∀ i < D, (Hh.hash (Spec.RsaPss.zeros 8 ++ mHash ++
          (List.range (db - (fnz (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)) db).getD 0 - 1)).map fun i =>
            vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)
              ((fnz (vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo)) db).getD 0 + 1 + i))).getD i 0 =
        vfz V6 ((maskV n₀.toNat).setWidth 8) (oEm + lo) (db + i)) ↔
    Spec.RsaPss.verify Hh Gh (n₀ :: rest) eB mHash sB (if fixed then some slen.toNat else none) = true := by
  subst hD
  have c1 : oEm = 0 := rfl
  have c2 : oSt = 3072 := rfl
  have hlo1 : lo ≤ 1 := hlo ▸ loV_le _
  generalize hx : (Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (Spec.RsaPss.zeros (rest.length + 1)) = x
    at hV3
  have hxl : x.length = rest.length + 1 := by
    rw [← hx]
    cases h : Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB with
    | none => exact VG.Proof.RsaPss.zeros_length _
    | some y => exact VG.Proof.RsaPss.publicOpChecked_length' h
  have hem : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) =
      rest.length + 1 - lo := by
    rw [VG.Proof.RsaPss.emLength_eq rest h0, hlo, loV]
    split <;> omega
  generalize hz : 8 * Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) -
    (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1) = z
  have hc : (maskV n₀.toNat).setWidth 8 = (0xFF : Byte) >>> z := by rw [maskV_eq rest h0, hz]
  generalize hc' : (maskV n₀.toNat).setWidth 8 = c at *
  generalize hk : rest.length + 1 = k at *
  have hDl := hHv.1
  have hL : k - lo - Hh.len - 1 = db := by omega
  have hV3' : ∀ i < k, V3 i = x.getD i 0 := fun i hi => by have := hV3 i hi; rwa [c1, Nat.zero_add] at this
  -- `DB`.
  have hmk : srcB V3 (oEm + lo + db) Hh.len = Any.vH Hh (x.drop lo) (k - lo - Hh.len - 1) := by
    rw [hL, Any.vH, List.drop_drop]
    refine range_take_drop (by omega) fun i hi => ?_
    rw [c1, Nat.zero_add, hV3' _ (by omega)]
  have hdbx : (List.range db).map (fun i => V3 (oEm + lo + i)) = (x.drop lo).take (k - lo - Hh.len - 1) := by
    rw [hL]; exact range_take_drop (by omega) fun i hi => by rw [c1, Nat.zero_add, hV3' _ (by omega)]
  have hmkl : (Spec.Mgf1.mgf1 Gh (srcB V3 (oEm + lo + db) Hh.len) db).length = db := Proof.Mgf1.mgf1_length hGv _ _
  generalize hdbL : Any.vDb Hh Gh (x.drop lo) (k - lo - Hh.len - 1) z = dbL
  have hdbl : dbL.length = db := by
    rw [← hdbL, Any.vDb, VG.Proof.RsaPss.clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hGv,
      List.length_take, List.length_drop]
    omega
  have hf : ∀ i < db, vfz V6 c (oEm + lo) i = dbL.getD i 0 := fun i hi => by
    have e1 : vfz V6 c (oEm + lo) i = upd (mixV V3 (Spec.Mgf1.mgf1 Gh (srcB V3 (oEm + lo + db) Hh.len) db) (oEm + lo) db)
        (oEm + lo) (mixV V3 (Spec.Mgf1.mgf1 Gh (srcB V3 (oEm + lo + db) Hh.len) db) (oEm + lo) db (oEm + lo) &&& c)
        (oEm + lo + i) := by
      simp only [vfz, upd]; rw [hV6 _ (by omega), hV6 _ (by omega)]
    rw [e1, hc, db_bytes _ _ hmkl i hi, ← hdbL, Any.vDb, hdbx, hmk, hL]
  have hfnz : fnz (vfz V6 c (oEm + lo)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [fnz_congr hf, ← hdbl, fnz_lz dbL _ (Nat.le_refl _)]
  have hsalt : ∀ p, p < db → (List.range (db - p - 1)).map (fun i => vfz V6 c (oEm + lo) (p + 1 + i)) =
      dbL.drop (p + 1) := fun p hp => by
    apply List.ext_getElem (by simp [hdbl]; omega)
    intro i h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [hf _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hH : ∀ i < Hh.len, vfz V6 c (oEm + lo) (db + i) = (Any.vH Hh (x.drop lo) (k - lo - Hh.len - 1)).getD i 0 :=
    fun i hi => by
      simp only [vfz, upd]
      rw [ifn (by omega), hV6 _ (by omega), mixV, ifn (by omega), Any.vH, hL, getD_take_drop hi,
        List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, ← hV3' _ (by omega)]
      congr 1; omega
  have hacc : acc0V (V3 (oEm + k - 1)) (V3 oEm) (V3 (oEm + lo)) c lo =
      acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo := by
    rw [c1, Nat.zero_add, Nat.zero_add, hV3' _ (by omega), hV3' _ (by omega), hV3' _ (by omega), hc]
  have hv := vlogic (G := Gh) hHv x mHash (k := k) (lo := lo) (z := z) fixed slen rfl hxl hlo1 (by omega) (by omega)
  dsimp only at hv
  rw [hdbL] at hv
  have hb := Any.verify_bytes Hh Gh hGv (n₀ := n₀) (rest := rest) (eB := eB) (sB := sB)
    (sLen := if fixed then some slen.toNat else none) hmH (by rw [hsB, List.length_cons, hk]) rfl rfl
    (lo := lo) (by rw [hem, List.length_cons, hk]; omega) hlo1 (by
      have : (if fixed then some slen.toNat else none).getD 0 = (if fixed then slen.toNat else 0) := by
        cases fixed <;> rfl
      rw [hem, this]; omega)
  rw [List.length_cons, hk, hx, hz, hem] at hb
  rw [hb, ← hv, hacc, hfnz, hL]
  by_cases hlt : lz dbL < db
  · simp only [ifp hlt, Option.isSome_some, Option.map_some, Option.getD_some, decide_eq_true hlt]
    rw [hsalt _ hlt, hf _ hlt]
    refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [hH i hi, hL]
  · simp only [ifn hlt, Option.isSome_none, Option.map_none, Option.getD_none, decide_eq_false hlt]
    rw [hsalt 0 (by omega)]
    refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [hH i hi, hL]

end VG.Proof.RsaPss.X86_64
