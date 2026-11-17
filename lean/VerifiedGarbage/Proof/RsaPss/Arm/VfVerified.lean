module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfAny
public import VerifiedGarbage.Proof.RsaPss.Arm.VfFixed
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.RsaPss.Arm.VfChk
public import VerifiedGarbage.Proof.HashTable.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.RsaPss.Arm.Table

/-! ### `RsaPss.Arm.VfMain`, which only this module used -/

section

/-! ### `RsaPss.Arm.VfLogic`, which only this module used -/

section

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

/-- `verify` with the hash function `H` and MGF1 with `G`, byte by byte. -/
theorem verify_bytes₂ (G H : Spec.Mgf1.Hash) (hG : Proof.Mgf1.Valid G) {n₀ : Byte} {rest eB mHash sB : List Byte}
    {sLen : Option Nat} (hm : mHash.length = H.len) (hs : sB.length = (n₀ :: rest).length) {emBits emLen lo : Nat}
    (hb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : Spec.RsaPss.emLength emBits = emLen)
    (hk : emLen + lo = (n₀ :: rest).length) (hlo : lo ≤ 1) (hfit : H.len + sLen.getD 0 + 2 ≤ emLen) :
    Spec.RsaPss.verify H G (n₀ :: rest) eB mHash sB sLen = true ↔
      (lo = 1 → ((Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (Spec.RsaPss.zeros (n₀ :: rest).length)).getD 0 0 = 0) ∧
      RsaPss.EncOk₂ G H mHash
        (((Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (Spec.RsaPss.zeros (n₀ :: rest).length)).drop lo)
        emLen (8 * emLen - emBits) sLen := by
  unfold Spec.RsaPss.verify
  simp only [hb, he, hs, beq_self_eq_true, Bool.true_and, show (n₀ :: rest).length - emLen = lo by omega_using [hk]]
  cases hp : Spec.Rsa.publicOpChecked (n₀ :: rest) eB sB with
  | none =>
    simp only [Option.getD_none, Bool.false_eq_true, false_iff, not_and]
    intro _ h
    have := h.1
    simp only [Spec.RsaPss.zeros, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_replicate] at this
    split at this <;> simp at this
  | some x =>
    have hx := RsaPss.publicOpChecked_length' hp
    simp only [Option.getD_some, Bool.and_eq_true, beq_iff_eq]
    rw [← he, RsaPss.verifyEncoding_bytes₂ G H hG hm (by rw [List.length_drop, hx]; omega_using [he, hk]) (by omega_using [he, hfit]), he]
    refine and_congr_left fun _ => ?_
    rcases (show lo = 0 ∨ lo = 1 by omega_using [hlo]) with rfl | rfl
    · simp [Spec.RsaPss.zeros]
    · obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (show x ≠ [] from fun h => by simp [h] at hx)
      simp [Spec.RsaPss.zeros]

/-- The result: `acc` is zero and the hash of `M'` is `H` exactly when the
encoding is valid. -/
theorem good_iff (P : EP) (hGv : Proof.Mgf1.Valid P.G) (τ : State) (hi : In h.D P τ) (hf : fits h P) {sB : List Byte}
    (hsB : sB.length = P.K)
    (hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB sB).getD (Spec.RsaPss.zeros P.K)).getD i 0 = emv P τ i) :
    (acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)) ↔
      Spec.RsaPss.verify h.G P.G P.nB P.eB (digB h P τ) sB (sLenO P) = true := by
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
  rw [show Spec.RsaPss.verify h.G P.G P.nB = Spec.RsaPss.verify h.G P.G (b :: rest) by rw [hbr],
    verify_bytes₂ P.G h.G hGv (emLen := P.K - lo P) (lo := lo P)
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
  have hmk : (Spec.Mgf1.mgf1 P.G (seedV h P τ) (dbN h P)).length = dbN h P := Mgf1.mgf1_length hGv _ _
  have htl : ((x.drop (lo P)).take (dbN h P)).length = dbN h P := by
    simp only [List.length_take, List.length_drop, hxl]; omega_arith
  have hvDb : RsaPss.vDb₂ P.G h.G (x.drop (lo P)) (dbN h P) z = dbL h P τ := by
    unfold RsaPss.vDb₂
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
  unfold RsaPss.EncOk₂
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

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the body

After the call, over the state `τ` it leaves (`rest_vp`): `acc`, the
unmasking (MGF1 through the table `mgf1`), the scan, and the path for the expected salt length; then the
result is `verify`'s (`fin_of`, by `good_iff`). The body (`body_vq`): the
checks, then 0 if something does not fit, or the call and the rest.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable (h : PssHash)

/-- The end of the body, over the state `τ` the call leaves. -/
abbrev GE (P : EP) (τ t : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ t ∧ K2 h P τ t.mem ∧
    t.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ) then 1 else 0

/-- The path for the expected salt length. -/
theorem tailIte_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => ((Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0)) ∧ s.syms = τ.syms)
      (.ite .eq (fixedPath f h.sh) (anyPath f h.sh)) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) := by
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.1.2, h₂.1.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P Q hP).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, ha⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_left ha]⟩, sy⟩
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P Q hP).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, trivial⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_right ha]⟩, sy⟩

/-- After the call. -/
theorem rest_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => W0 h P τ s ∧ s.syms = τ.syms) (.seq (.block accSet) (.seq (.block acc0) (.seq (mgfPart fg h.sh 15)
      (.seq (.block topSet) (.seq (.block topAnd) (.seq (.block scanSet) (.seq (countLoop scanBody)
        (.seq (.block posSet) (.seq (.block posChk) (.seq (.block anySet)
          (.ite .eq (fixedPath f h.sh) (anyPath f h.sh))))))))))))
      (fun τ s => GE h P τ s ∧ s.syms = τ.syms) :=
  VP.assoc ((VP.syms (acc_vp h P hP)).seq ((vmask_vp h P Q hP).seq (VP.assoc ((VP.syms (vtop_vp h P hP)).seq
    ((VP.syms (scanSet_vp h P hP)).seq ((VP.syms (scan_vp h P hP (X := Kd h P) fun _ _ hk => hk.2.1)).seq
      (VP.assoc ((VP.syms (pos_vp h P hP)).seq ((VP.syms (anySet_vp h P hP)).seq (tailIte_vp h P Q hP))))))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) (hGv : Proof.Mgf1.Valid P.G) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) :
    Fin h P.G P σ t := by
  obtain ⟨⟨hc, hi, hf, -⟩, hcr⟩ := hv
  obtain ⟨hc', hk, r0⟩ := hg
  have st : (P.lay h.D).St σ t :=
    ⟨hc.st.ok, hc'.st.sp, hc'.st.rd.trans hc.st.rd, hc'.st.wr.trans hc.st.wr, hc.st.frame.trans hc'.st.frame⟩
  refine ⟨⟨hi, st⟩, fun hpre => ?_⟩
  have hw := hcr hpre
  have hxb : Spec.Rsa.bytesAt τ.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K =
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K) := by
    revert hw
    cases Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ) with
    | none => exact fun hw => hw.2
    | some y => exact fun hw => hw.2
  have hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K)).getD i 0 =
      emv P τ i := fun i hi' => by
    rw [← hxb, bytesAt_getD hi', (call_geo h hi).1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdig : digB h P τ = digB h P σ := hc.st.ro (R := P.DIG h.D) (by simp)
  have g := good_iff h P hGv τ hk.1 hf (bytesAt_length _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- The body. -/
theorem body_vq {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (c : PdImpl) :
    VQ (fun σ s => S h P σ s ∧ s.syms = σ.syms) (verifyBody f fg h.sh c.name c.code) (Fin h P.G P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩)
  have hGv : Proof.Mgf1.Valid P.G := Q.gG ▸ g.valid
  show VQ _ (.seq (.block (verifyChk h.sh)) (.seq (.block (params ++ expLen ++ saltFits))
    (.ite .ne (.block [mw .r0 0]) (.seq (.block pubArgs) (.seq (.call c.name c.code) _))))) _
  refine VQ.seq (VP.syms (chk_vp h P)) (VQ.seq (VP.syms (par_vp h P)) (VQ.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2.2, h₂.1.2.2.2.2.2.2])
    (VQ.of_vp ((VP.syms (fail_vp h P.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x.1)) ?_))
  exact VQ.seq ((VP.syms (pa_vp h P)).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨m0_of h h1 e, sy⟩) fun _ _ h => h)
    (VQ.seq (VP.syms (call_vp h P c)) (VQ.reidx (rest_vp h P Q hP) (fun σ s ⟨hv, sy⟩ => ⟨w0_self h Q hv sy, rfl⟩)
      fun σ τ t ⟨hv, _⟩ hg => fin_of h P hGv hv hg.1))

end VG.Proof.RsaPss.Arm.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: verified

Before the body (`body_vq`), the index of the table `hash` chooses the body
for its hash function's shape (`tab_vq`, by `byLen_vq`, RSAES-OAEP's
`byLen_vp` for a piece with nothing after it). The frames around it
(`wrap_ok`, `wrap_ct`), the result as the shared contract states it, with
`hash` any of the tables of `MdHash` of `mvs` and `mgf1` any of the tables
of `MdHash` of `vs`: `vg_rsa_pss_verify_precomputed`, calling a precomputed
public operation `c`, is verified (`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (OHash tA wp_ldrT St_roR St_roW wp_cmpR1 ofNat_sub_beq32)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

theorem VQ.mono {F F' G G' : State → State → Prop} {c : Prog isa} (h : VQ F c G) (hF : ∀ σ s, F' σ s → F σ s)
    (hG : ∀ σ s, G σ s → G' σ s) : VQ F' c G' :=
  ⟨fun σ s hs => WP.mono (h.1 σ s (hF σ s hs)) fun t ht => hG σ t ht,
    h.2.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ _ => trivial⟩

/-- `byLen` from bodies with nothing after them, with the digest length `D`
in `r1`, which a `cmp` keeps: the branch of `D`. -/
theorem byLen_vq {F G : State → State → Prop} {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 32)
    (h1 : ∀ σ s, F σ s → s.gpr .r1 = BitVec.ofNat 32 D) (hst : ∀ σ s v, F σ s → F σ (subFlags s (s.gpr .r1) v))
    (hb : VQ F (b D) G) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 2 ^ 32 ∧ encodable (BitVec.ofNat 32 x) = true ∧
      ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.cmp .r1 (.imm (BitVec.ofNat 32 x))]) hc).isSome
        = true) → VQ F (Impl.RsaOaep.Arm.byLen b ds) G
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, hen, htx⟩ := hx x (List.mem_cons_self ..)
    refine VQ.seq (G := fun σ s => F σ s ∧ isa.eval .eq s = some (decide (D = x)))
      (VP.taint [] htx (fun _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) fun σ s hs =>
        WP.mono (wp_cmpR1 hen) fun t e => ?_) ?_
    · subst e
      refine ⟨hst σ s _ hs, ?_⟩
      show some (s.gpr .r1 - BitVec.ofNat 32 x == 0) = some (decide (D = x))
      rw [h1 σ s hs, ofNat_sub_beq32 hD hx0]
    refine VQ.ite (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun σ s hs => hs.1.1) fun _ _ h => h
      · exact VQ.of_vp (VP.of_imp (p := False) (fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e) False.elim)
    · by_cases hDx : D = x
      · exact VQ.of_vp (VP.of_imp (p := False) (fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e) False.elim)
      · exact (byLen_vq hD h1 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono (fun σ s hs => hs.1.1) fun _ _ h => h

variable (h : PssHash)

/-- The load of the table's word 5. -/
theorem idxWord_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block [.ldr .r1 .r1 20]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The comparisons of the index in `r1` with each of `idxs`. -/
theorem idxs_certs : ∀ x ∈ idxs, x < 2 ^ 32 ∧ encodable (BitVec.ofNat 32 x) = true ∧
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.cmp .r1 (.imm (BitVec.ofNat 32 x))]) hc).isSome =
      true := by
  intro x hx
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, _, by taint_decide⟩

/-- The index of the hash function of the table `hash` to `r1`. -/
theorem idx_vp {g : OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P) :
    VP (Sy (S h P)) (.block (idxLoad 14))
      (fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (Spec.HashTable.index h.G)) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.htbl
  have keep : ∀ σ s v, Sy (S h P) σ s → Sy (S h P) σ (s.setReg .r1 v) := fun σ s v ⟨⟨hi, st⟩, sy⟩ =>
    ⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩
  show VP _ (.block ([Impl.RsaPss.Arm.ld .r1 (arg 14)] ++ [.ldr .r1 .r1 20])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = P.hd)
    (VP.ldrSp (c := [(.r1, arg 14)]) (fun _ _ _ _ h₁ h₂ => h₁.1.2.sp.trans h₂.1.2.sp.symm)
      fun σ s hs => ?_)
    (VP.taint [.r1] idxWord_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · obtain ⟨⟨hi, st⟩, -⟩ := id hs
    obtain ⟨a14, r14, v14⟩ := argAt hi st (j := 14) (by decide)
    replace v14 : s.mem.readW ((P.lay h.D).fr (arg 14)) 32 = P.hd := v14
    have hw : WP isa (.block [.ldrSp .r1 (arg 14)]) s fun t => t = s.setReg .r1 P.hd := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec, arg_lt (show 14 < 16 by decide), ↓reduceIte, State.load32, st.sp, a14,
        r14, v14, Option.map_some, runStep_some, runBlock_nil]
      simp
    refine WP.mono hw fun t e => ?_
    subst e
    exact ⟨keep σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨hs2, h1⟩ := hs
    have T := Q.ht σ hs2.1.1.htabT
    refine WP.mono (wp_ldrT (by decide) h1 (St_roR hs2.1.2 tRo (tC 20 (by decide)))
      ((St_roW hs2.1.2 tRo (tC 20 (by decide))).trans T.ix)) fun t e => ?_
    subst e
    exact ⟨keep σ s _ hs2, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The body for the hash function of the table `hash`, whose shape its
index gives. -/
theorem tab_vq {g : OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hsh : h.sh = ofIdx (Spec.HashTable.index h.G)) (hidx : Spec.HashTable.index h.G ∈ idxs) (c : PdImpl) :
    VQ (Sy (S h P)) (verifyTab f fg c.name c.code) (Fin h P.G P) := by
  refine VQ.seq (idx_vp h P Q) (byLen_vq (D := Spec.HashTable.index h.G) (by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hidx
    rcases hidx with e | e | e | e | e | e | e | e <;> rw [e] <;> decide)
    (fun _ _ hs => hs.2) (fun σ s v ⟨⟨⟨hi, st⟩, sy⟩, r1⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩, r1⟩) ?_
    hidx idxs_certs)
  rw [← hsh]
  exact (body_vq h P Q c).mono (fun _ _ hs => hs.1) fun _ _ x => x

/-- A table of `MdHash`'s facts in a state with the same statics and words. -/
theorem htab_keep {dn : String} {f : MdFns} {p ai ac ad : BitVec 32} {σ s : State} (H : HTab h dn f p ai ac ad σ)
    (sy : s.syms = σ.syms) (hm : ∀ o, o + 4 ≤ 44 → s.mem.readW (tA p o) 32 = σ.mem.readW (tA p o) 32) :
    HTab h dn f p ai ac ad s :=
  ⟨by rw [sy]; exact H.i, by rw [sy]; exact H.c, by rw [sy]; exact H.d, (hm 0 (by decide)).trans H.m0,
    (hm 12 (by decide)).trans H.m3, (hm 16 (by decide)).trans H.m4, (hm 20 (by decide)).trans H.ix⟩

/-- A table of `Hash`'s facts in a state with the same statics and words. -/
theorem tabFacts_keep {G : Impl.Pbkdf2.Stream.Arm.Hash} {f : Impl.RsaOaep.Arm.Fns} {p ai au af : BitVec 32} {σ s : State}
    (T : RsaOaep.Arm.TabFacts G f p ai au af σ) (sy : s.syms = σ.syms)
    (hm : ∀ o, o + 4 ≤ 44 → s.mem.readW (tA p o) 32 = σ.mem.readW (tA p o) 32) :
    RsaOaep.Arm.TabFacts G f p ai au af s := by
  have m := T.mem
  unfold RsaOaep.Arm.TabMem at m
  refine ⟨by rw [sy]; exact T.ok, ?_, (hm 24 (by decide)).trans T.d, by rw [sy]; exact T.ai, by rw [sy]; exact T.au,
    by rw [sy]; exact T.af⟩
  unfold RsaOaep.Arm.TabMem
  rw [sy, hm 0 (by decide), hm 4 (by decide), hm 8 (by decide)]
  exact m

variable (mvs : List MVar) (vs : List TVar)

/-- The code, calling `c`, with the hash function any of the tables of
`MdHash` of `mvs` and MGF1's any of the tables of `MdHash` of `vs`. -/
abbrev verifyCode (c : PdImpl) : Prog isa :=
  verifyPrecomputed (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) c.name c.code

/-- The contract, with those tables. -/
abbrev vspec : Contract isa := spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)

variable {mvs vs}

/-- The tables, as the contract gives them: one of `hs` at the stack argument
10 and one of `ts` at 11, with the functions of distinct names at distinct
addresses, and the digest's length that of the former's hash function. -/
theorem spec_tab {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 32 s.mem (State.addr (stackArg s 10)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 11)) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 10).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 11).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 10)) (stackArg s 1) := by
  verify_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr nS eS dS gS sR sTH sT sA kN kE kD kG kS kR kTH kT kA fN fE fD fG fS fR
    fTH fT kv el1 elK glK scrK rlK
  exact ⟨hheld, hheld2, hpw, fTH, fT, h⟩

theorem spec_sp {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) : stackBytes ≤ s.sp.toNat := by
  verify_pre at h
  exact h.1

/-- The public parameters for the hash function's table of `w` and MGF1's of
`wg`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep wg.g.G s (s'.syms w.h.H.md.st.initN) (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w))
    (HTab w.h (MdHashTable.Arm.digName w) (MdHashTable.Arm.fnsOf mvs) (stackArg s 10) (s'.syms w.h.H.md.st.initN)
      (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w)))
    (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (RsaOaep.Arm.TabFacts wg.g.H (HashTable.Arm.fnsOf vs) (stackArg s 11) (s'.syms wg.g.H.initN)
      (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN))

theorem gne_of {w : TVar} (hw : w ∈ vs) : (HashTable.Arm.fnsOf vs).init ≠ [] ∧ (HashTable.Arm.fnsOf vs).upd ≠ [] ∧
    (HashTable.Arm.fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [HashTable.Arm.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

theorem fne_of {w : MVar} (hw : w ∈ mvs) : (MdHashTable.Arm.fnsOf mvs).init ≠ [] ∧
    (MdHashTable.Arm.fnsOf mvs).comp ≠ [] ∧ (MdHashTable.Arm.fnsOf mvs).dig ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [MdHashTable.Arm.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The digest's length is that of `w`'s hash function. -/
theorem dl_of {s : State} {w : MVar} (hfit : (stackArg s 10).toNat + 44 ≤ 2 ^ 32)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 10)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hdl : Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 10)) (stackArg s 1)) :
    (stackArg s 1).toNat = w.h.D := by
  rw [hdl _ (MdHashTable.Arm.hashAt_tableOf hfit (MdHashTable.Arm.held_tableOf hfit hh).2.2.2), w.h.glen]

/-- The entry state, for the tables of `w` at the stack argument 10 and `wg`
at 11, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_state (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) {s s' : State}
    (hs : (vspec mvs vs).pre s) {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 10)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hhg : Abi.tableHeld 32 s.mem (State.addr (stackArg s 11)) (FnTable.words isa s (HashTable.Arm.tableOf wg)))
    (hsy : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s.syms n = s'.syms n) :
    Sy (S w.h (epw (mvs := mvs) (vs := vs) s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfit, hfitg, hdl⟩ := spec_tab hs
  have hD := dl_of hfit hh hdl
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_sp hs)
  have ok := (in_of_pre (G := wg.g.G) (hi := 0) (hc := 0) (hdg := 0) (HT := fun _ => True) (ai := 0) (au := 0)
    (af := 0) (T := fun _ => True) hs hD trivial trivial).ok
  rw [ep_lay] at ok
  have hn := MdHashTable.Arm.mem_names hw
  have hng := Proof.HashTable.Arm.mem_names hwg
  have ht := MdHashTable.Arm.htab_entered ok hsp' (p := stackArg s 10) (by simp [ep]) hfit hc hpwH hw hh
  have tf := Proof.HashTable.Arm.tabFacts_entered ok hsp' (p := stackArg s 11) (by simp [ep]) hfitg hcg hpwG hwg hhg
  rw [hsy _ (List.mem_append_left _ hn.1), hsy _ (List.mem_append_left _ hn.2.1),
    hsy _ (List.mem_append_left _ hn.2.2)] at ht
  rw [hsy _ (List.mem_append_right _ hng.1), hsy _ (List.mem_append_right _ hng.2.1),
    hsy _ (List.mem_append_right _ hng.2.2)] at tf
  have hi := in_of_pre (G := wg.g.G) (hi := s'.syms w.h.H.md.st.initN) (hc := s'.syms w.h.H.md.compN)
    (hdg := s'.syms (MdHashTable.Arm.digName w)) (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN)
    (af := s'.syms wg.g.H.finN) hs hD ht tf
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

/-- What the body needs of the tables of `w` and `wg`. -/
theorem tf_of {s s' : State} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs) :
    TF w.h wg.g (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (MdHashTable.Arm.digName w)
      (epw (mvs := mvs) (vs := vs) s s' w wg) :=
  ⟨fun _ x => x, fun _ x => x, fne_of hw, gne_of hwg, rfl, fun _ _ x sy hm => htab_keep w.h x sy hm,
    fun _ _ x sy hm => tabFacts_keep x sy hm⟩

theorem code_ok (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (c : PdImpl) {s : State}
    (hs : (vspec mvs vs).pre s) :
    WP isa (verifyCode mvs vs c) s fun t => abiPreserved s t ∧ (vspec mvs vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, ⟨Tg, hTg, hhg⟩, -, hfit, hfitg, hdl⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  have hD := dl_of hfit hh hdl
  have hidx := (MdHashTable.Arm.held_tableOf hfit hh).2.2.2
  have hidxg := (Proof.HashTable.Arm.held_tableOf hfitg hhg).2.1
  have st := entered_state hc hcg hs hw hwg hh hhg (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hsp; omega_using [hsp]
  let P := epw (mvs := mvs) (vs := vs) s s w wg
  have hb := (tab_vq w.h P (tf_of hw hwg) w.shape w.mem c).1 _ _ st
  refine WP.mono (wrap_ok (by decide) (by omega_using [hsp']) (W := (P.lay w.h.D).W)
    (Q := fun r _ => Res w.h wg.g.G P (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 48) (argv := P.argv w.h.D) (ro := (P.lay w.h.D).ro)
      (rw := (P.lay w.h.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 10) = State.addr (stackArg s 10) from rfl,
      MdHashTable.Arm.hashAt_tableOf hfit hidx, Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 11) = State.addr (stackArg s 11) from rfl,
      Proof.HashTable.Arm.hashAt_tableOf hfitg hidxg, Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (P.lay w.h.D).ro) =>
      entered_ro (F := frameBytes) (A := 48) (argv := P.argv w.h.D) (rw := (P.lay w.h.D).rw) hin.ok hsp' hR
    have hDg : digB w.h P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) w.h.D :=
      ro (R := P.DIG w.h.D) (by simp)
    have hSg : sigB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2))
        (s.gpr .r1).toNat := by
      have e : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 2)) P.gl =
          Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) P.gl := ro (R := P.SIG) (by simp)
      rw [hin.glK] at e
      exact e
    unfold Res at res
    rw [hDg, hSg] at res
    rw [w.h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (c : PdImpl) :
    ConstantTime isa (vspec mvs vs).pre (vspec mvs vs).pub (verifyCode mvs vs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, ⟨Tg, hTg, hhg₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, htabg, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhg₂ := (htabg _ _ rfl rfl _ hTg).mp hhg₁
  have hsy' : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by
      rcases List.mem_append.mp hn with e | e
      · exact List.mem_append_left _ e
      · exact List.mem_append_right _ (List.mem_append_left _ e))).symm
  have hep : epw (mvs := mvs) (vs := vs) s₁ s₁ w wg = epw (mvs := mvs) (vs := vs) s₂ s₁ w wg := by
    obtain ⟨hab, hwd⟩ := List.append_inj hl (by simp [bytesAt_length, h1, h3])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h1])
    have hw' := map_toNat_inj hwd
    simp only [ep]
    rw [hsp, h0, h1, h2, h3, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
    rw [h0, h1] at hn
    rw [h2, h3] at he
    rw [a8, a9] at hw'
    rw [show State.addr (s₂.gpr .r0) = BitVec.setWidth 64 (s₂.gpr .r0) from rfl, hn,
      show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, he,
      show State.addr (stackArg s₂ 8) = BitVec.setWidth 64 (stackArg s₂ 8) from rfl, hw']
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; have := spec_sp h₁; simp only [stackBytes] at this; omega_using [this]) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (tab_vq w.h (epw (mvs := mvs) (vs := vs) s₁ s₁ w wg) (tf_of hw hwg) w.shape w.mem c).2.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc hcg h₁ hw hwg hh₁ hhg₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc hcg h₂ hw hwg hh₂ hhg₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_verify_precomputed`, calling `c`, with the hash function any
of the tables of `MdHash` of `mvs` and MGF1's any of the tables of `MdHash` of
`vs`, meets the shared contract (satisfiable, `VfSat.lean`). -/
theorem verify_verified (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs)
    (hsat : ∃ s, (vspec mvs vs).pre s) (c : PdImpl) : Verified target (verifyCode mvs vs c) (vspec mvs vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc hcg c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc hcg c, hsat⟩

end VG.Proof.RsaPss.Arm.Vf
