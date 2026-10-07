import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB2

/-!
# RSASSA-PSS verification on AArch64: what the result means

`vlogic`: `x0` after `cmpH` (`resV`, from `acc0V`, `acc1V` and the hash of
`M'`) is 1 exactly when the encoding is valid, byte by byte
(`VerifyCases.lean`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.Spec.Mgf1 VG.Impl.RsaPss.AArch64

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem xor_eq_zero64 (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := BitVec.xor_eq_zero_iff

theorem zext_inj (a b : Byte) : BitVec.setWidth 64 a = BitVec.setWidth 64 b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · rintro rfl; rfl

theorem zext_eq_zero (a : Byte) : BitVec.setWidth 64 a = 0 ↔ a = 0 := zext_inj a 0

theorem ff_bit (i : Nat) (hi : i < 64) : (255#64)[i] = decide (i < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  by_cases h : i < 8
  · revert h; revert i; decide
  · rw [decide_eq_false h]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (255#64).toNat < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem zext_and_not (top c : Byte) :
    BitVec.setWidth 64 top &&& (BitVec.setWidth 64 c ^^^ 255#64) = BitVec.setWidth 64 (top &&& ~~~c) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_setWidth, ff_bit i hi]
  by_cases h : i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (by omega : 8 ≤ i)]

theorem acc0V_eq_zero (V : Nat → Byte) (k : Nat) {lo : Nat} (c : Byte) (hlo : lo ≤ 1) :
    acc0V V k lo c = 0 ↔ V (oEm + k - 1) = 0xbc ∧ (lo = 1 → V oEm = 0) ∧ V (oEm + lo) &&& ~~~c = 0 := by
  unfold acc0V
  rw [or_eq_zero64, or_eq_zero64, xor_eq_zero64,
    show (BitVec.ofNat 64 0xbc : BitVec 64) = BitVec.setWidth 64 (0xbc : Byte) from rfl, zext_inj,
    show (BitVec.ofNat 64 0xFF : BitVec 64) = 255#64 from rfl, zext_and_not, zext_eq_zero]
  rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
  · simp only [show 0#64 - BitVec.ofNat 64 0 = 0 from rfl]
    simp
  · simp only [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, zext_eq_zero]
    simp [and_assoc]

theorem acc1V_eq_zero (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) :
    acc1V a0 f db any sv = 0 ↔ a0 = 0 ∧ nzV f db = 1 ∧ nz f db ≠ none ∧
      (any = 0 → sv = BitVec.ofNat 64 (db - (nz f db).getD 0 - 1)) := by
  unfold acc1V
  rw [or_eq_zero64, or_eq_zero64, or_eq_zero64, xor_eq_zero64,
    show (1#64 : BitVec 64) = BitVec.setWidth 64 (1 : Byte) from rfl, zext_inj]
  by_cases h : nz f db = none
  · simp [h]
  · rw [ite_eq_right h, show (0 : BitVec 64) >>> 63 = 0 from rfl]
    by_cases ha : any = 0 <;> simp [ha, h, and_assoc]

theorem orF_eq_zero (g : Nat → BitVec 64) : ∀ j, orF g j = 0 ↔ ∀ i < j, g i = 0
  | 0 => by simp [orF]
  | j + 1 => by
    rw [orF, or_eq_zero64, orF_eq_zero g j]
    constructor
    · rintro ⟨hi, hj⟩ i hi'
      exact if e : i = j then e ▸ hj else hi i (by omega)
    · intro hi
      exact ⟨fun i hi' => hi i (by omega), hi j (by omega)⟩

theorem lt_or {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) : (x ||| y).toNat < 2 ^ n := by
  rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow hx hy

theorem lt_xor {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) : (x ^^^ y).toNat < 2 ^ n := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow hx hy

theorem lt_and {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) : (x &&& y).toNat < 2 ^ n := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_left hx

theorem lt_byte (b : Byte) {n : Nat} (hn : 8 ≤ n) : (b.setWidth 64).toNat < 2 ^ n := by
  rw [BitVec.toNat_setWidth]
  have := b.isLt
  have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

theorem lt_ofNat {a n : Nat} (ha : a < 2 ^ n) : (BitVec.ofNat 64 a).toNat < 2 ^ n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha

theorem orF_lt (g : Nat → BitVec 64) {n : Nat} (hg : ∀ i, (g i).toNat < 2 ^ n) : ∀ j, (orF g j).toNat < 2 ^ n
  | 0 => by simp [orF]; exact Nat.two_pow_pos n
  | j + 1 => lt_or (orF_lt g hg j) (hg j)

/-- `(y - 1) >>> 63`: 1 exactly when `y = 0`, for `y < 2⁶³`. -/
theorem top_sub (y : BitVec 64) (hy : y.toNat < 2 ^ 63) : (y - 1#64) >>> 63 = if y = 0 then 1#64 else 0#64 := by
  by_cases h : y = 0
  · subst h; decide
  · rw [ite_eq_right h]
    have h0 : y.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show (2 ^ 64 - 1 % 2 ^ 64 + y.toNat) % 2 ^ 64 = y.toNat - 1 by omega]
    exact Nat.div_eq_of_lt (by omega)

theorem nz_lz (l : List Byte) : ∀ j ≤ l.length, nz (fun i => l.getD i 0) j = if lz l < j then some (lz l) else none
  | 0, _ => by simp [nz]
  | j + 1, hj => by
    have ih := nz_lz l j (by omega)
    simp only [nz, ih]
    by_cases h : lz l < j
    · rw [ifp h]; exact (ifp (show lz l < j + 1 by omega) _ _).symm
    · rw [ifn h]
      by_cases h' : lz l = j
      · subst h'
        rw [ifn (getD_lz_ne (by omega)), ifp (by omega)]
      · rw [ifp (getD_lt_lz (by omega)), ifn (by omega)]

section
variable {G : Hash} (hG : Proof.Mgf1.Valid G) {D : Nat} (hGl : G.len = D) {x : List Byte} {V : Nat → Byte}
  {k lo db : Nat} (hx : x.length = k) (hV : ∀ i < k, V (oEm + i) = x.getD i 0) (hdb : lo + db + D + 1 = k)

include hGl hx hV hdb in
/-- `H` in `EM`. -/
theorem vH_view : vH G (x.drop lo) db = (List.range D).map fun i => V (oEm + lo + db + i) := by
  unfold vH
  refine eq_range_map (by simp only [List.length_take, List.length_drop, hx]; omega) fun i hi => ?_
  rw [show oEm + lo + db + i = oEm + (lo + db + i) by omega, hV _ (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ifp (by omega)]
  congr 2
  omega

include hG hGl hx hV hdb in
/-- `DB` in `EM`, unmasked and its top bits cleared. -/
theorem vDb_view {c : Byte} {z : Nat} (hc : c = (0xFF : Byte) >>> z) :
    ∀ i < db, wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i) =
      (vDb G (x.drop lo) db z).getD i 0 := by
  intro i hi
  have hmk : mkB G D V (oEm + lo) db = mgf1 G (vH G (x.drop lo) db) db := by
    rw [vH_view hGl hx hV hdb]; rfl
  have hml := Proof.Mgf1.mgf1_length hG (vH G (x.drop lo) db) db
  have ht : ((x.drop lo).take db).length = db := by simp only [List.length_take, List.length_drop, hx]; omega
  have hxi : ∀ j < db, ((x.drop lo).take db).getD j 0 = V (oEm + lo + j) := fun j hj => by
    rw [Nat.add_assoc, hV _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ifp hj]
  unfold vDb
  rw [clearTop_getD, hmk, hc]
  unfold wct upd mixV
  by_cases h0 : i = 0
  · subst h0
    rw [ifp rfl, ifp (by omega), ifp (by omega), xorBytes_getD (by omega) (by omega), hxi 0 hi]
    simp only [Nat.add_zero, Nat.sub_self]
  · rw [ifn h0, ifn (by omega), ifp (by omega), xorBytes_getD (by omega) (by omega), hxi i hi]
    congr 2
    omega

end

theorem lt_shr63 (x : BitVec 64) : (x >>> 63).toNat < 2 ^ 11 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have : x.toNat / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by omega)
  omega

/-- What `cmpH` ORs is below `2¹¹`. -/
theorem acc_lt (V : Nat → Byte) (k lo : Nat) (c : Byte) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64)
    (g : Nat → BitVec 64) (D : Nat) (hdb : db < 2 ^ 11) (hs : any = 0 → sv.toNat < 2 ^ 11)
    (hg : ∀ i, (g i).toNat < 2 ^ 11) :
    (acc1V (acc0V V k lo c) f db any sv ||| orF g D).toNat < 2 ^ 63 := by
  have h11 : (2 : Nat) ^ 11 < 2 ^ 63 := by decide
  have hb : ∀ b : Byte, (b.setWidth 64).toNat < 2 ^ 11 := fun b => lt_byte b (by decide)
  have h0 : (acc0V V k lo c).toNat < 2 ^ 11 := by
    unfold acc0V
    exact lt_or (lt_or (lt_xor (hb _) (lt_ofNat (by decide))) (lt_and (hb _))) (lt_and (hb _))
  have h1 : (acc1V (acc0V V k lo c) f db any sv).toNat < 2 ^ 11 := by
    unfold acc1V
    refine lt_or (lt_or h0 (lt_or (lt_xor (hb _) (by decide)) (lt_shr63 _))) ?_
    split
    · rename_i ha
      exact lt_xor (hs ha) (lt_ofNat (by omega))
    · exact Nat.two_pow_pos 11
  exact Nat.lt_trans (lt_or h1 (orF_lt g hg D)) h11

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega)
    intro i h₁ h₂
    have := h i (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem eq_ofNat_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : b = BitVec.ofNat 64 a ↔ b.toNat = a := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- The salt after the first nonzero byte of `DB` (`f`, `dbL`). -/
theorem msgV_eq {f : Nat → Byte} {dbL : List Byte} {db : Nat} (hl : dbL.length = db)
    (hf : ∀ i < db, f i = dbL.getD i 0) (mH : List Byte) {p : Nat} (hp : p < db) :
    msgV mH f db p = Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (p + 1) := by
  unfold msgV
  refine congrArg (_ ++ ·) (eq_range_map (by rw [List.length_drop, hl]; omega) fun i hi => ?_).symm
  rw [hf _ (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `x0` after `cmpH` is 1 exactly when the encoding in `x` is valid. -/
theorem vlogic {G : Hash} (hG : Proof.Mgf1.Valid G) {D : Nat} (hGl : G.len = D) {x : List Byte} {V : Nat → Byte}
    {k lo db : Nat} (hx : x.length = k) (hV : ∀ i < k, V (oEm + i) = x.getD i 0) (hdb : lo + db + D + 1 = k)
    (hdb1 : 1 ≤ db) (hlo : lo ≤ 1) (hk : k ≤ 1024) {mH : List Byte} (hm : mH.length = D) {c : Byte} {z : Nat}
    (hc : c = (0xFF : Byte) >>> z) {any sv : BitVec 64} (hs : any = 0 → sv.toNat < db) {b : Bool}
    (hb : b = true ↔ (lo = 1 → x.getD 0 0 = 0) ∧
      EncOk G mH (x.drop lo) (k - lo) z (if any = 0 then some sv.toNat else none)) :
    resV (acc1V (acc0V V k lo c) (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv)
      (G.hash (msgV mH (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db
        ((nz (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)))
      (wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c) (oEm + lo) db D = if b then 1#64 else 0#64 := by
  have hf := vDb_view hG hGl hx hV hdb hc
  have hH : ∀ i < D, wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + db + i) =
      (vH G (x.drop lo) db).getD i 0 := fun i hi => by
    rw [vH_view hGl hx hV hdb]
    unfold wct upd mixV
    rw [ifn (by omega), ifn (by omega), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have e1 : V (oEm + k - 1) = (x.drop lo).getD (k - lo - 1) 0 := by
    rw [show oEm + k - 1 = oEm + (k - 1) by omega, hV _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  have e2 : V oEm = x.getD 0 0 := hV 0 (by omega)
  have e3 : V (oEm + lo) = (x.drop lo).getD 0 0 := by
    rw [hV _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  have hvl : (vH G (x.drop lo) db).length = D := by rw [vH_view hGl hx hV hdb, List.length_map, List.length_range]
  have hdbl : (vDb G (x.drop lo) db z).length = db := by
    rw [vDb, clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hG]
    simp only [List.length_take, List.length_drop, hx]; omega
  generalize wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c = W at hf hH ⊢
  rw [resV, top_sub _ (acc_lt V k lo c _ db any sv _ D (by omega) (fun h => by have := hs h; omega)
    (fun i => lt_xor (lt_byte _ (by decide)) (lt_byte _ (by decide))))]
  suffices hy : acc1V (acc0V V k lo c) (fun i => W (oEm + lo + i)) db any sv |||
      orF (fun i => BitVec.setWidth 64 ((G.hash (msgV mH (fun i => W (oEm + lo + i)) db
        ((nz (fun i => W (oEm + lo + i)) db).getD 0))).getD i 0) ^^^ BitVec.setWidth 64 (W (oEm + lo + db + i))) D = 0 ↔
      (lo = 1 → x.getD 0 0 = 0) ∧ EncOk G mH (x.drop lo) (k - lo) z (if any = 0 then some sv.toNat else none) by
    rw [← hb] at hy
    by_cases h : b = true
    · rw [ifp (hy.mpr h), ifp h]
    · rw [ifn (fun e => h (hy.mp e)), ifn h]
  unfold EncOk
  rw [show k - lo - G.len - 1 = db by omega]
  generalize vDb G (x.drop lo) db z = dbL at hf hdbl ⊢
  have hnz : nz (fun i => W (oEm + lo + i)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [nz_congr hf, nz_lz dbL db (by omega)]
  have hnzV : nzV (fun i => W (oEm + lo + i)) db = if lz dbL < db then dbL.getD (lz dbL) 0 else 0 := by
    rw [nzV_congr hf]
    unfold nzV
    rw [nz_lz dbL db (by omega)]
    by_cases hp : lz dbL < db
    · rw [ifp hp, ifp hp]
    · rw [ifn hp, ifn hp]
  rw [or_eq_zero64, acc1V_eq_zero, acc0V_eq_zero _ _ _ hlo, orF_eq_zero, hnz, hnzV, e1, e2, e3, ← hc]
  by_cases hp : lz dbL < db
  · simp only [hp, ↓reduceIte, Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    rw [msgV_eq hdbl hf mH hp]
    have hz : ∀ i < D, (BitVec.setWidth 64 ((G.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0) ^^^
        BitVec.setWidth 64 (W (oEm + lo + db + i)) = 0) ↔
        (G.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0 = (vH G (x.drop lo) db).getD i 0 :=
      fun i hi => by rw [xor_eq_zero64, zext_inj, hH i hi]
    rw [show (∀ i < D, BitVec.setWidth 64 ((G.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0) ^^^
        BitVec.setWidth 64 (W (oEm + lo + db + i)) = 0) ↔ _ from forall₂_congr hz,
      ← list_eq_iff_getD (by rw [hG.2, hGl]) hvl]
    have hsl : ∀ {any : BitVec 64}, (any = 0 → sv = BitVec.ofNat 64 (db - lz dbL - 1)) ↔
        ((if any = 0 then some sv.toNat else none) = none ∨
          (if any = 0 then some sv.toNat else none) = some (db - 1 - lz dbL)) := fun {any} => by
      by_cases ha : any = 0
      · simp only [ha, ite_true, reduceCtorEq, false_or, Option.some.injEq, true_implies]
        rw [eq_ofNat_iff (by omega)]
        omega
      · rw [ite_eq_right ha]
        exact ⟨fun _ => .inl rfl, fun _ h => absurd h ha⟩
    rw [hsl]
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, hS⟩, hH'⟩
      exact ⟨hP, hA, hB, hC, hS, hH'⟩
    · rintro ⟨hP, hA, hB, hC, hS, hH'⟩
      exact ⟨⟨⟨hA, hP, hB⟩, hC, hS⟩, hH'⟩
  · rw [ifn hp, ifn hp]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; exact absurd rfl h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hp

end VG.Proof.RsaPss.AArch64
