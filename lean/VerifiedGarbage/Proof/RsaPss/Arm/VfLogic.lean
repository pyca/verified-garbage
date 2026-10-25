module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfAny
public import VerifiedGarbage.Proof.RsaPss.Arm.VfFixed
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the result

`acc` is zero and the hash of `M'` is `H` exactly when the encoding is
valid (`good_iff`): `acc`'s bits are the checks of `EncOk`
(`Proof/RsaPss/VerifyCases.lean`), one by one (`acc2_iff`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm

variable (h : PssHash)

theorem bc_iff : ∀ a : Byte, a.setWidth 32 ^^^ 0xbc = 0 ↔ a = 0xbc := by decide
theorem one_iff : ∀ a : Byte, a.setWidth 32 ^^^ 1 = 0 ↔ a = 1 := by decide
theorem zero_iff : ∀ a : Byte, a.setWidth 32 = 0 ↔ a = 0 := by decide
theorem top_iff : ∀ j < 9, ∀ b : Byte, (b.setWidth 32 &&& (BitVec.ofNat 32 (2 ^ j - 1) ^^^ 0xFF) = 0 ↔
    b &&& ~~~((BitVec.ofNat 32 (2 ^ j - 1)).setWidth 8) = 0) := by decide

/-- The mask of a first byte not zero, `2^j - 1`. -/
theorem cW_cases {b : Byte} (hb : b.toNat ≠ 0) : ∃ j < 9, cW (b.setWidth 32) = BitVec.ofNat 32 (2 ^ j - 1) := by
  rw [setWidth_byte]
  obtain ⟨-, h1, h2⟩ := params_table b.toNat b.isLt
  by_cases e : b.toNat = 1
  · exact ⟨8, by decide, by rw [h1 e]; rfl⟩
  · obtain ⟨j, hj, -, -, he⟩ := h2 (by omega_arith)
    exact ⟨j, by omega_arith, he⟩

theorem or0 (x y : BitVec 32) : (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := BitVec.or_eq_zero_iff

/-- `acc`'s bits, the checks. -/
theorem acc2_iff (P : EP) (τ : State) (hlo : lo P ≤ 1) (hb : (n0 P).toNat ≠ 0) (hdb : dbN h P < 2 ^ 32)
    (hsl : P.slt < 2 ^ 32) :
    acc2 h P τ = 0 ↔ (emv P τ (P.K - 1) = 0xbc ∧ (lo P = 1 → emv P τ 0 = 0) ∧
      emv P τ (lo P) &&& ~~~((cW ((n0 P).setWidth 32)).setWidth 8) = 0) ∧
      (lzF h P τ < dbN h P ∧ dbF h P τ (lzF h P τ) = 1 ∧ (P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt)) := by
  have e0 : ((emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P)) = 0) ↔ (lo P = 1 → emv P τ 0 = 0) := by
    rcases (show lo P = 0 ∨ lo P = 1 by omega_arith) with e | e <;> rw [e]
    · simp
    · rw [show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, zero_iff]
      simp
  obtain ⟨j, hj, hc⟩ := cW_cases hb
  have ht := top_iff j hj (emv P τ (lo P))
  simp only [acc2, accW, or0, and_assoc]
  rw [hc, bc_iff, ht, e0]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases hf : lzF h P τ < dbN h P
  · have p1 : pzJ h P τ (dbN h P) = lzF h P τ := by simp only [pzJ, hf, ite_true]
    have p2 : vzJ h P τ (dbN h P) = dbF h P τ (lzF h P τ) := by simp only [vzJ, hf, ite_true]
    have p3 : nfJ h P τ (dbN h P) = 0 := by simp only [nfJ, hf, ite_true]
    simp only [pzF, p1, p2, p3, show (0 : BitVec 32) >>> 31 = 0 by decide, hf, true_and]
    refine and_congr (one_iff _) ?_
    by_cases ha : P.any = 0
    · simp only [anyW, ha, ite_true, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
        true_implies]
      have xz : ∀ x y : BitVec 32, x ^^^ y = 0 ↔ x = y := fun x y => BitVec.xor_eq_zero_iff
      rw [xz, Offset.ofNat_sub_ofNat (w := 32) (by omega_arith),
        show BitVec.ofNat 32 (dbN h P - lzF h P τ) - 1 = BitVec.ofNat 32 (dbN h P - lzF h P τ - 1) from
          by rw [show dbN h P - lzF h P τ = (dbN h P - lzF h P τ - 1) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)]
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt hsl] at this
      · intro e; rw [e]
    · have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
      simp only [anyW, ha, ite_false, show (1 : BitVec 32) - 1 = 0 by decide, az, false_implies]
  · have p3 : nfJ h P τ (dbN h P) = BitVec.allOnes 32 := by simp only [nfJ, hf, ite_false]
    simp only [p3, show BitVec.allOnes 32 >>> 31 = (1 : BitVec 32) by decide, hf, false_and, iff_false]
    exact fun ⟨_, h1, _⟩ => absurd h1 (by decide)

theorem list_eq_iff {l₁ l₂ : List Byte} {n : Nat} (h₁ : l₁.length = n) (h₂ : l₂.length = n) :
    l₁ = l₂ ↔ ∀ i < n, l₁.getD i 0 = l₂.getD i 0 := by
  refine ⟨fun e _ _ => by rw [e], fun e => List.ext_getElem (by omega_arith) fun i a b => ?_⟩
  have := e i (by omega_arith)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem a, List.getElem?_eq_getElem b] using this

theorem HOk_iff (P : EP) (τ : State) (x : List Byte) : HOk h P τ x ↔ h.G.hash x = seedV h P τ := by
  rw [h.hash, list_eq_iff (n := h.D) (by rw [← h.hash, h.valid.2, h.glen]) (by simp [seedV])]

/-- `M'`, when `DB`'s padding ends where it should. -/
theorem M_eq {P : EP} {τ : State} (hf : lzF h P τ < dbN h P) (hs : P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt) :
    (if P.any = 0 then Mf h P τ else Ma h P τ) =
      Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (lzF h P τ + 1) := by
  by_cases ha : P.any = 0
  · rw [ite_eq_left ha, Mf]
    have hs := hs ha
    refine congrArg (Spec.RsaPss.zeros 8 ++ digB h P τ ++ ·) (RsaPss.eq_range_map (by rw [List.length_drop, dbL_length]; omega_arith)
      fun i hi => ?_).symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, dbL_getD h (by omega_arith)]
    congr 1; omega_arith
  · rw [ite_eq_right ha, Ma]
    simp only [pzF, pzJ, hf, ite_true]

/-- The result: `acc` is zero and the hash of `M'` is `H` exactly when the
encoding is valid. -/
theorem good_iff (P : EP) (τ : State) (hi : In h.D P τ) (hf : fits h P) {sB : List Byte} (hsB : sB.length = P.K)
    (hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB sB).getD (Spec.RsaPss.zeros P.K)).getD i 0 = emv P τ i) :
    (acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)) ↔
      Spec.RsaPss.verify h.G h.G P.nB P.eB (digB h P τ) sB (sLenO P) = true := by
  have hl := nB_length hi
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  have hbt : b.toNat ≠ 0 := hn0 ▸ hf.1
  have hb0 : b ≠ 0 := fun e => hbt (by rw [e]; rfl)
  rw [hbr, List.length_cons] at hl
  have hem := emLen_eq hbr hl hbt
  have hG := h.valid
  have gl : h.G.len = h.D := h.glen
  have hcz := cW_byte hb0 rest
  rw [hem] at hcz
  have hs0 : (sLenO P).getD 0 = eLen P := by unfold sLenO eLen; split <;> rfl
  rw [show Spec.RsaPss.verify h.G h.G P.nB = Spec.RsaPss.verify h.G h.G (b :: rest) by rw [hbr],
    RsaPss.verify_bytes h.G hG (emLen := P.K - lo P) (lo := lo P)
      (by unfold digB; rw [bytesAt_length, gl]) (by rw [hsB, List.length_cons]; omega_arith) rfl hem
      (by rw [List.length_cons]; omega_arith) hlo (by rw [gl, hs0]; omega_arith)]
  generalize hz : 8 * (P.K - lo P) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = z at hcz ⊢
  replace hcz : (cW ((n0 P).setWidth 32)).setWidth 8 = (0xFF : Byte) >>> z := by rw [hn0]; exact hcz
  have hx' : ∀ i < P.K, ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD
      (Spec.RsaPss.zeros (b :: rest).length)).getD i 0 = emv P τ i := by
    rw [List.length_cons, hl, ← hbr]; exact hx
  have hxl : ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD
      (Spec.RsaPss.zeros (b :: rest).length)).length = P.K := by
    cases e : Spec.Rsa.publicOpChecked (b :: rest) P.eB sB with
    | none => rw [Option.getD_none, RsaPss.zeros_length, List.length_cons]; omega_arith
    | some y => rw [Option.getD_some, RsaPss.publicOpChecked_length' e, List.length_cons]; omega_arith
  generalize ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD (Spec.RsaPss.zeros (b :: rest).length)) = x
    at hx' hxl ⊢
  have hdrop : ∀ i, lo P + i < P.K → (x.drop (lo P)).getD i 0 = emv P τ (lo P + i) := fun i hi' => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, hx' _ hi']
  have hL : P.K - lo P - h.G.len - 1 = dbN h P := by rw [gl]
  have hvH : RsaPss.vH h.G (x.drop (lo P)) (dbN h P) = seedV h P τ := by
    unfold RsaPss.vH
    refine RsaPss.eq_range_map (by simp only [List.length_take, List.length_drop, hxl, gl]; omega_arith) fun i hi' => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by rw [gl]; exact hi'), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, hdrop _ (by omega_arith), Nat.add_assoc]
  have ht : ∀ j < dbN h P, ((x.drop (lo P)).take (dbN h P)).getD j 0 = emv P τ (lo P + j) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD, hdrop _ (by omega_arith)]
  have hmk : (Spec.Mgf1.mgf1 h.G (seedV h P τ) (dbN h P)).length = dbN h P := Mgf1.mgf1_length hG _ _
  have htl : ((x.drop (lo P)).take (dbN h P)).length = dbN h P := by
    simp only [List.length_take, List.length_drop, hxl]; omega_arith
  have hvDb : RsaPss.vDb h.G (x.drop (lo P)) (dbN h P) z = dbL h P τ := by
    unfold RsaPss.vDb
    rw [hvH]
    refine RsaPss.eq_range_map (by rw [RsaPss.clearTop_length, Mgf1.xorBytes_length, hmk, htl]; omega_arith)
      fun i hi' => ?_
    rw [RsaPss.clearTop_getD]
    by_cases e : i = 0
    · subst e
      rw [ite_eq_left rfl, RsaPss.xorBytes_getD (by omega_arith) (by omega_arith), ht 0 (by omega_arith), ← hcz]
      simp only [dbF, ite_true, Nat.add_zero]
    · rw [ite_eq_right e, RsaPss.xorBytes_getD (by omega_arith) (by omega_arith), ht i hi']
      simp only [dbF, e, ite_false]
  have hlz : RsaPss.lz (dbL h P τ) = lzF h P τ := rfl
  unfold RsaPss.EncOk
  rw [hL, hvDb, hvH, hlz, hdrop _ (by omega_arith), hdrop 0 (by omega_arith), show lo P + (P.K - lo P - 1) = P.K - 1 by omega_arith,
    Nat.add_zero, hx' 0 (by omega_arith), ← hcz, acc2_iff h P τ hlo hf.1 (by omega_arith) hi.slt32, HOk_iff]
  constructor
  · rintro ⟨⟨⟨a1, a0, a2⟩, f, v, sl⟩, hm⟩
    rw [M_eq h f sl] at hm
    refine ⟨a0, a1, a2, f, by rw [dbL_getD h f]; exact v, ?_, hm⟩
    unfold sLenO
    by_cases ha : P.any = 0
    · rw [ite_eq_left ha]; right; have := sl ha; congr 1; omega_arith
    · rw [ite_eq_right ha]; left; rfl
  · rintro ⟨a0, a1, a2, f, v, sl, hm⟩
    have sl' : P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt := fun ha => by
      unfold sLenO at sl
      rw [ite_eq_left ha] at sl
      rcases sl with sl | sl
      · exact absurd sl (by simp)
      · have := Option.some.inj sl; omega_arith
    exact ⟨⟨⟨a1, a0, a2⟩, f, by rw [← dbL_getD h f]; exact v, sl'⟩, by rw [M_eq h f sl']; exact hm⟩

end VG.Proof.RsaPss.Arm.Vf
