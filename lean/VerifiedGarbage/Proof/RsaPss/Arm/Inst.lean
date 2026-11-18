module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfFixed
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
public import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Proof.Rsa.PreKey
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
public import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.RsaPss.Arm.Table
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees

/-! ### `RsaPss.Arm.VfVerified`, which only this module used -/

section

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

end

end

/-! ### `RsaPss.Arm.SgVerified`, which only this module used -/

section

/-!
# RSASSA-PSS signing on ARMv7: verified

The body for the hash function `h` of the table `hash` and MGF1's `g` of
the table `mgf1` (`body_vp`): the checks, then zeros and 0 if something does
not fit, or the encoding and the call. Before it, the table's index chooses
the body for `h`'s shape (`tab_vp`, by RSAES-OAEP's `byLen_vp`). The frames
around it (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, with `hash` any of the tables of `MdHash` of `mvs` and `mgf1` any of the
tables of `MdHash` of `vs`: `vg_rsa_pss_sign`, calling `vg_rsa_private_checked`
over any implementation `v` of `vg_rsa_private_crt`, is verified
(`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (OHash tA wp_ldrT St_roR St_roW byLen_vp)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

variable (h : PssHash)

theorem body_vp (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signBody f fg h.sh (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h g.G P)) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk h.sh)) (.seq (.block (params ++ saltFits)) (.ite .ne signFail
    (.seq (signEnc f fg h.sh) (.seq (.block privArgs)
      (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v))))))) _
  exact (VP.syms (chk_vp h P)).seq ((VP.syms (par_vp h P)).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (((enc_vp h P Q hP).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩) fun _ _ h => h).seq
      ((VP.syms (pa_vp h g.G P)).seq (VP.syms (call_vp h g P v))))))

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
    VP (Sy (S h P)) (.block (idxLoad 22))
      (fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (Spec.HashTable.index h.G)) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.htbl
  have keep : ∀ σ s v, Sy (S h P) σ s → Sy (S h P) σ (s.setReg .r1 v) := fun σ s v ⟨⟨hi, st⟩, sy⟩ =>
    ⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩
  show VP _ (.block ([Impl.RsaPss.Arm.ld .r1 (arg 22)] ++ [.ldr .r1 .r1 20])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = P.hd)
    (VP.ldrSp (c := [(.r1, arg 22)]) (fun _ _ _ _ h₁ h₂ => h₁.1.2.sp.trans h₂.1.2.sp.symm)
      fun σ s hs => ?_)
    (VP.taint [.r1] idxWord_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · obtain ⟨⟨hi, st⟩, -⟩ := id hs
    obtain ⟨a22, r22, v22⟩ := argAt hi st (j := 22) (by decide)
    replace v22 : s.mem.readW ((P.lay h.D).fr (arg 22)) 32 = P.hd := v22
    have hw : WP isa (.block [.ldrSp .r1 (arg 22)]) s fun t => t = s.setReg .r1 P.hd := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec, arg_lt (show 22 < 24 by decide), ↓reduceIte, State.load32, st.sp, a22,
        r22, v22, Option.map_some, runStep_some, runBlock_nil]
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
theorem tab_vp (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hsh : h.sh = ofIdx (Spec.HashTable.index h.G)) (hidx : Spec.HashTable.index h.G ∈ idxs)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signTab f fg (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h g.G P)) := by
  refine (idx_vp h P Q).seq (byLen_vp (D := Spec.HashTable.index h.G) (by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hidx
    rcases hidx with e | e | e | e | e | e | e | e <;> rw [e] <;> decide)
    (fun _ _ hs => hs.2) (fun σ s v ⟨⟨⟨hi, st⟩, sy⟩, r1⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩, r1⟩) ?_
    hidx idxs_certs)
  rw [← hsh]
  exact (body_vp h g P Q v).mono (fun _ _ hs => hs.1) fun _ _ x => x

variable (mvs : List MVar) (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `MdHash` of `mvs` and MGF1's any of the tables
of `MdHash` of `vs`. -/
abbrev signCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  sign (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

/-- The contract, with those tables. -/
abbrev sspec : Contract isa := spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)

variable {mvs vs}

/-- The tables, as the contract gives them: one of `hs` at the stack argument
18 and one of `ts` at 19, with the functions of distinct names at distinct
addresses, and the digest's length that of the former's hash function. -/
theorem spec_tab {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 18).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 19).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13) := by
  sign_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA nS eS pS qS dpS dqS qiS dS
    slS sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fTH fT kv olk
    el1 elK pl1 plK ql1 qlK dpl qil dql slK
  exact ⟨hheld, hheld2, hpw, fTH, fT, h⟩

theorem spec_sp {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) : stackBytes ≤ s.sp.toNat := by
  sign_pre at h
  exact h.1

/-- The public parameters for the hash function's table of `w` and MGF1's of
`wg`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.md.st.initN) (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w))
    (HTab w.h (MdHashTable.Arm.digName w) (MdHashTable.Arm.fnsOf mvs) (stackArg s 18) (s'.syms w.h.H.md.st.initN)
      (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w)))
    (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (RsaOaep.Arm.TabFacts wg.g.H (HashTable.Arm.fnsOf vs) (stackArg s 19) (s'.syms wg.g.H.initN)
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
theorem dl_of {s : State} {w : MVar} (hfit : (stackArg s 18).toNat + 44 ≤ 2 ^ 32)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hdl : Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13)) :
    (stackArg s 13).toNat = w.h.D := by
  rw [hdl _ (MdHashTable.Arm.hashAt_tableOf hfit (MdHashTable.Arm.held_tableOf hfit hh).2.2.2), w.h.glen]

/-- The entry state, for the tables of `w` at the stack argument 18 and `wg`
at 19, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_state (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) {s s' : State}
    (hs : (sspec mvs vs).pre s) {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hhg : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (HashTable.Arm.tableOf wg)))
    (hsy : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s.syms n = s'.syms n) :
    Sy (S w.h (epw (mvs := mvs) (vs := vs) s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfit, hfitg, hdl⟩ := spec_tab hs
  have hD := dl_of hfit hh hdl
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_sp hs)
  have ok := (in_of_pre (hi := 0) (hc := 0) (hdg := 0) (HT := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs hD trivial trivial).ok
  rw [ep_lay] at ok
  have hn := MdHashTable.Arm.mem_names hw
  have hng := Proof.HashTable.Arm.mem_names hwg
  have ht := MdHashTable.Arm.htab_entered ok hsp' (p := stackArg s 18) (by simp [ep]) hfit hc hpwH hw hh
  have tf := Proof.HashTable.Arm.tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [ep]) hfitg hcg hpwG hwg hhg
  rw [hsy _ (List.mem_append_left _ hn.1), hsy _ (List.mem_append_left _ hn.2.1),
    hsy _ (List.mem_append_left _ hn.2.2)] at ht
  rw [hsy _ (List.mem_append_right _ hng.1), hsy _ (List.mem_append_right _ hng.2.1),
    hsy _ (List.mem_append_right _ hng.2.2)] at tf
  have hi := in_of_pre (hi := s'.syms w.h.H.md.st.initN) (hc := s'.syms w.h.H.md.compN)
    (hdg := s'.syms (MdHashTable.Arm.digName w)) (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN)
    (af := s'.syms wg.g.H.finN) hs hD ht tf
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

/-- What the body needs of the tables of `w` and `wg`. -/
theorem tf_of {s s' : State} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs) :
    TF w.h wg.g (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (MdHashTable.Arm.digName w)
      (epw (mvs := mvs) (vs := vs) s s' w wg) :=
  ⟨fun _ x => x, fun _ x => x, fne_of hw, gne_of hwg⟩

/-- Unfolds the contract's postcondition. -/
macro "sign_post" : tactic => `(tactic| (
  sig_post [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]))

theorem code_ok (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) {s : State}
    (hs : (sspec mvs vs).pre s) :
    WP isa (signCode mvs vs v) s fun t => abiPreserved s t ∧ (sspec mvs vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, ⟨Tg, hTg, hhg⟩, -, hfit, hfitg, hdl⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  have hD := dl_of hfit hh hdl
  have hidx := (MdHashTable.Arm.held_tableOf hfit hh).2.2.2
  have hidxg := (Proof.HashTable.Arm.held_tableOf hfitg hhg).2.1
  have st := entered_state hc hcg hs hw hwg hh hhg (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  let P := epw (mvs := mvs) (vs := vs) s s w wg
  have hb := (tab_vp w.h wg.g P (tf_of hw hwg) w.shape w.mem v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (P.lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G P (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)
    (hQ := fun _ m₁ m₂ hf hres => by
      have fit := hin.ok.fits P.OUT (List.mem_append_right _ List.mem_cons_self)
      exact writtenOutcome_frame hf
        (released_apart (F := frameBytes) (A := 80) (C := 3440) (argv := P.argv w.h.D) (ro := (P.lay w.h.D).ro)
          (rw := (P.lay w.h.D).rw) hin.ok hsp' (R := P.OUT) (Or.inr (by simp)))
        (by change P.OUT.len ≤ 2 ^ 64; omega_using [fit]) hres)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 80) (C := 3440) (argv := P.argv w.h.D) (ro := (P.lay w.h.D).ro)
      (rw := (P.lay w.h.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sign_post
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 18) = State.addr (stackArg s 18) from rfl,
      MdHashTable.Arm.hashAt_tableOf hfit hidx, Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl,
      Proof.HashTable.Arm.hashAt_tableOf hfitg hidxg, Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (P.lay w.h.D).ro) =>
      entered_ro (F := frameBytes) (A := 80) (C := 3440) (argv := P.argv w.h.D) (rw := (P.lay w.h.D).rw) hin.ok
        hsp' hR
    have hP : pB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
      ro (R := P.PP) (by simp)
    have hQ : qB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
      ro (R := P.QQ) (by simp)
    have hDP : dpB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        (stackArg s 3).toNat := ro (R := P.DP) (by simp)
    have hDQ : dqB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8))
        (stackArg s 5).toNat := ro (R := P.DQ) (by simp)
    have hQI : qiB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10))
        (stackArg s 3).toNat := ro (R := P.QI) (by simp)
    have hDg : digB w.h P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 12)) w.h.D :=
      ro (R := P.DIG w.h.D) (by simp)
    have hS : saltB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 14))
        (stackArg s 15).toNat := ro (R := P.SALT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hDg, hS] at res
    rw [w.h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (sspec mvs vs).pre (sspec mvs vs).pub (signCode mvs vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, ⟨Tg, hTg, hhg₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  sig_pub [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, htabg, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhg₂ := (htabg _ _ rfl rfl _ hTg).mp hhg₁
  have hsy' : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by
      rcases List.mem_append.mp hn with e | e
      · exact List.mem_append_left _ e
      · exact List.mem_append_right _ (List.mem_append_left _ e))).symm
  have hep : epw (mvs := mvs) (vs := vs) s₁ s₁ w wg = epw (mvs := mvs) (vs := vs) s₂ s₁ w wg := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3])
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a8, a10, a12, a14, a15, a16, a17, a18, a19]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (tab_vp w.h wg.g (epw (mvs := mvs) (vs := vs) s₁ s₁ w wg) (tf_of hw hwg) w.shape w.mem v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc hcg h₁ hw hwg hh₁ hhg₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc hcg h₂ hw hwg hh₂ hhg₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the
hash function any of the tables of `MdHash` of `mvs` and MGF1's any of the
tables of `MdHash` of `vs`, meets the shared contract (satisfiable,
`SgSat.lean`). -/
theorem sign_verified (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (hsat : ∃ s, (sspec mvs vs).pre s)
    (v : Proof.Rsa.Arm.CrtImpl) : Verified target (signCode mvs vs v) (sspec mvs vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc hcg v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc hcg v, hsat⟩

end VG.Proof.RsaPss.Arm.Sg

end

end

/-! ### `RsaPss.Arm.SgP`, which only this module used -/

section

/-!
# `vg_rsa_pss_sign_precomputed` on ARMv7

`vg_rsa_pss_sign`'s code (`signP`) calling `vg_rsa_private_checked_precomputed`
with the key's precomputed values `pre` and `pre_len`, our arguments 24 and
25, as its stack arguments 16 and 17 (`privArgsP`): the slots `sS` and `sL`,
which nothing reads after the call. The layout is `vg_rsa_pss_sign`'s with
`pre` among the buffers read and our two more arguments (`PreP`), and the
body's proofs are `vg_rsa_pss_sign`'s but for the call (`pa2_vp`, `call_vpP`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (OHash byLen_vp)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- What a layout given `pre` has: `pre` among the buffers read, our two
more arguments, and what the entry state holds of `pre`. -/
structure PreP (P : EP) : Prop where
  x : P.X = [⟨State.addr P.pre, P.prl * 8⟩]
  xa : P.xargs = [P.pre, BitVec.ofNat 32 P.prl]
  prl32 : P.prl < 2 ^ 32
  prlv : P.prl = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  px : P.PX = fun σ => Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) =
      some (Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.prl) ∧
    Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr P.pre) P.K = P.preL

/-- `pre`, a buffer only read. -/
abbrev EP.PRE (P : EP) : Region := ⟨State.addr P.pre, P.prl * 8⟩

theorem PreP.mem {D : Nat} {P : EP} (hP : PreP P) : P.PRE ∈ (P.lay D).ro := by
  simp [hP.x]

/-- Our arguments 24 and 25, `pre` and `pre_len`. -/
theorem argAtX {D : Nat} {P : EP} {σ s : State} (hP : PreP P) (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat}
    (hj : j = 24 ∨ j = 25) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = (P.lay D).argv.getD j 0 := by
  obtain hl : j < (P.lay D).argv.length := by
    simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil]; omega_using [hj]
  have hA := hi.ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + P.A; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

variable (h : PssHash)

/-- `pre` and `pre_len` to the call's stack arguments 16 and 17. -/
theorem pa2_wp (P : EP) (hP : PreP P) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64, Impl.RsaPss.Arm.ld .r4 (arg 25), st .r4 68]) s
      fun t => t.mem = (s.mem.writeW ((P.lay h.D).fr 64) P.pre).writeW ((P.lay h.D).fr 68)
          (BitVec.ofNat 32 P.prl) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r1 = s.gpr .r1 ∧
        t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 := by
  have hg := hi.geo
  obtain ⟨a24, r24, v24⟩ := argAtX hP hi hc.st (j := 24) (.inl rfl)
  obtain ⟨a25, r25, v25⟩ := argAtX hP hi hc.st (j := 25) (.inr rfl)
  replace v24 : s.mem.readW ((P.lay h.D).fr (arg 24)) 32 = P.pre := by
    rw [v24]; simp [EP.argv, hP.xa]
  replace v25 : s.mem.readW ((P.lay h.D).fr (arg 25)) 32 = BitVec.ofNat 32 P.prl := by
    rw [v25]; simp [EP.argv, hP.xa]
  obtain wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  obtain rd25 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW ((P.lay h.D).fr 64) v).readW ((P.lay h.D).fr (arg 25)) 32 = m.readW ((P.lay h.D).fr (arg 25)) 32 :=
    fun m v => Lay.readW_fr_other _ m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; decide)
      (by decide) (by decide)
  obtain l24 : arg 24 < 4096 := by decide
  obtain l25 : arg 25 < 4096 := by decide
  prun [sp0, Impl.RsaPss.Arm.ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, l24, l25, a24, r24, v24, a25, r25, v25,
    rd25]

/-- Before the call of `vg_rsa_private_checked_precomputed`. -/
abbrev R1P (G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop :=
  (P.lay h.D).St σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024) ∧
    stackArg s 16 = P.pre ∧ stackArg s 17 = BitVec.ofNat 32 P.prl

theorem pa2_vp (G : Spec.Mgf1.Hash) (P : EP) (hP : PreP P) :
    VP (R1 h G P) (.block [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64, Impl.RsaPss.Arm.ld .r4 (arg 25),
      st .r4 68]) (R1P h G P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he, pa⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  refine WP.mono (pa2_wp h P hP hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  obtain ⟨σ', ok⟩ := hg.ok
  obtain fr : Frame [⟨(P.lay h.D).fr 64, 8⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 64) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  obtain rd0 : ∀ (u : State), u.sp = s.sp → ∀ i, i < 18 → stackArg u i = u.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro u hu i hi'
    simp only [stackArg, stackArgAddr, hu, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega_arith)]
  obtain keep : ∀ i, i < 16 → stackArg t i = stackArg s i := fun i hi' => by
    rw [rd0 t sp i (by omega_using [hi']), rd0 s rfl i (by omega_using [hi']), m, Lay.readW_fr_other _ _ _ (by omega_using [hi']) (by omega_using [hi']) (by decide),
      Lay.readW_fr_other _ _ _ (by omega_using [hi']) (by omega_using [hi']) (by decide)]
  refine ⟨hc.st.write fr (fun r hr => ?_) rd wr sp, hk.keep h fr fun r hr => ?_, fun i hi' => ?_,
    { pa with
      r0 := t0.trans pa.r0, r1 := t1.trans pa.r1, r2 := t2.trans pa.r2, r3 := t3.trans pa.r3
      a0 := (keep 0 (by decide)).trans pa.a0, a1 := (keep 1 (by decide)).trans pa.a1
      a2 := (keep 2 (by decide)).trans pa.a2, a3 := (keep 3 (by decide)).trans pa.a3
      a4 := (keep 4 (by decide)).trans pa.a4, a5 := (keep 5 (by decide)).trans pa.a5
      a6 := (keep 6 (by decide)).trans pa.a6, a7 := (keep 7 (by decide)).trans pa.a7
      a8 := (keep 8 (by decide)).trans pa.a8, a9 := (keep 9 (by decide)).trans pa.a9
      a10 := (keep 10 (by decide)).trans pa.a10, a11 := (keep 11 (by decide)).trans pa.a11
      a12 := (keep 12 (by decide)).trans pa.a12, a13 := (keep 13 (by decide)).trans pa.a13
      a14 := (keep 14 (by decide)).trans pa.a14, a15 := (keep 15 (by decide)).trans pa.a15 }, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 64 + 8 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  · rw [← he i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (d := 64) (k := 8) (by have := hi'; have := hi.k1024; unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  · rw [rd0 t sp 16 (by decide), m, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [rd0 t sp 17 (by decide), m, Mem.readW_writeW_self32]

section
variable {h}

theorem leak_st {P : EP} (hP : PreP P) {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  have px := hi.pxT
  rw [hP.px] at px
  obtain le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hP.prlv, Spec.Rsa.privatePrecomputedWords]; omega_using []
  obtain rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [← px.2]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem key_st {P : EP} (hP : PreP P) {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K)
      (Spec.Rsa.bytesAt s.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.q) P.ql) =
    some (Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.prl) := by
  have px := hi.pxT
  rw [hP.px] at px
  obtain rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [nB_at h hi hs, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp), rw]
  exact px.1

end

theorem call_preP {G : Spec.Mgf1.Hash} {P : EP} (hP : PreP P) {σ s : State} (hr : R1P h G P σ s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRdP P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.pre
        P.K P.el P.pl P.ql P.prl) (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hs, hk, -, pa, a16, a17⟩ := hr
  have hi := hk.1
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  have hA := ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  obtain oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
  obtain hPm := hP.mem (D := h.D)
  refine priv_preP pa a16 a17 hP.prl32 hs.sp hB (by simp only [frameBytes] at fit; omega_arith) ?_
    (oS.sub_right sS') ?_ ?_ hP.prlv (key_st hP hi hs)
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact oS.sub_right sI
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) hPm
    · rw [q0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := 0) (n := 72) (by show 0 + 72 ≤ frameBytes + 56; decide)).symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
    · exact dIS.symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.PP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QI) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) hPm).sub_left sS'
    · rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 72)
        (by show 0 + 72 ≤ frameBytes + 56; decide)).symm).sub_left sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = (P.lay h.D).LOW := rfl
    rw [low]
    simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · exact ok.low_buf (R := P.PRE) (.inl hPm)
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega_arith
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega_arith
    · exact fs (List.mem_append_left _ hPm)

/-- `out` and the result: the call of `vg_rsa_private_checked_precomputed`. -/
theorem call_vpP (g : RsaOaep.Arm.OHash) (P : EP) (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1P h g.G P) (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (Fin h g.G P) := by
  refine VG.Proof.RsaPkcs1Sig.Arm.VP.callC (fun s h => Proof.Rsa.Arm.private_contract_correctP v s h) (Proof.Rsa.Arm.private_contract_ctP v)
    (privCodeP_stack v)
    (privRdP P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
    (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_preP h hP hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hs, hk, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    obtain hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega_arith)⟩
    obtain hout : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    obtain wr' : Covers (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hout.cons (by rw [e2]; exact inS (by unfold oRsa; omega_arith))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons ((hro P.PRE hP.mem).cons
        (Covers.cons ?_ Covers.nil)))))))
    · rw [e1]; exact (inS (by unfold oEm; omega_arith)).right
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 72 ≤ frameBytes; decide))).right
  · rw [hr.1.sp]; exact hr.2.1.1.ok.B56
  · obtain ⟨hs₁, hk₁, -, pa₁, p16, p17⟩ := h₁
    obtain ⟨hs₂, hk₂, -, pa₂, q16, q17⟩ := h₂
    exact priv_pubP pa₁ pa₂ (by rw [hs₁.sp, hs₂.sp]) p16 q16 p17 q17
      (by rw [nB_at h hk₁.1 hs₁, nB_at h hk₂.1 hs₂]) (by rw [eB_at h hk₁.1 hs₁, eB_at h hk₂.1 hs₂])
      (by rw [leak_st hP hk₁.1 hs₁, leak_st hP hk₂.1 hs₂]) _ _
  · obtain ⟨hs, hk, he, pa, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    obtain st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hi, st⟩, ?_⟩
    obtain em : Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K =
        (List.range P.K).map (emF h g.G P σ) := by
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have := priv_postP pa po
    rw [nB_at h hi hs, eB_at h hi hs, em, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp),
      hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp), hs.ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h g hi hk.2.1]
    exact this

theorem body_vpP (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signBodyP f fg h.sh (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v))
      (Sy (Fin h g.G P)) := by
  by_cases hP' : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP' ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk h.sh)) (.seq (.block (params ++ saltFits)) (.ite .ne signFail
    (.seq (signEnc f fg h.sh) (.seq (.block (privArgs ++ [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64,
      Impl.RsaPss.Arm.ld .r4 (arg 25), st .r4 68]))
      (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v))))))) _
  exact (VP.syms (chk_vp h P)).seq ((VP.syms (par_vp h P)).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (((enc_vp h P Q hP').mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩) fun _ _ h => h).seq
      ((VP.syms (VP.block_append (pa_vp h g.G P) (pa2_vp h g.G P hP))).seq (VP.syms (call_vpP h g P hP v))))))

/-- The body for the hash function of the table `hash`, whose shape its
index gives. -/
theorem tab_vpP (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hsh : h.sh = ofIdx (Spec.HashTable.index h.G)) (hidx : Spec.HashTable.index h.G ∈ idxs) (hP : PreP P)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signTabP f fg (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (Sy (Fin h g.G P)) := by
  refine (idx_vp h P Q).seq (byLen_vp (D := Spec.HashTable.index h.G) (by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hidx
    rcases hidx with e | e | e | e | e | e | e | e <;> rw [e] <;> decide)
    (fun _ _ hs => hs.2) (fun σ s v ⟨⟨⟨hi, st⟩, sy⟩, r1⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩, r1⟩) ?_
    hidx idxs_certs)
  rw [← hsh]
  exact (body_vpP h g P Q hP v).mono (fun _ _ hs => hs.1) fun _ _ x => x

/-! ## The entry -/

/-- The contract, with the hash function one of the tables `hs`, MGF1's one of
`ts`, and the stack `vg_rsa_pss_sign` uses. -/
abbrev specP (hs ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "sign_preP" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, `ep`'s with `pre`. -/
def epP (s : State) (hi hc hdg : BitVec 32) (HT : State → Prop) (ai au af : BitVec 32) (T : State → Prop) : EP :=
  { ep s hi hc hdg HT ai au af T with
    X := [⟨State.addr (stackArg s 20), (stackArg s 21).toNat * 8⟩]
    A := 88
    xargs := [stackArg s 20, BitVec.ofNat 32 (stackArg s 21).toNat]
    pre := stackArg s 20
    prl := (stackArg s 21).toNat
    preL := Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat
    PX := fun σ => Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat) =
        some (Spec.Rsa.wordsAt σ.mem (State.addr (stackArg s 20)) (stackArg s 21).toNat) ∧
      Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat =
        Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat }

variable {hi hc hdg : BitVec 32} {HT : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem epP_lay (D : Nat) (s : State) :
    (epP s hi hc hdg HT ai au af T).lay D = layOf frameBytes 88
      ((epP s hi hc hdg HT ai au af T).argv D ++ [stackArg s 20, BitVec.ofNat 32 (stackArg s 21).toNat])
      ([(epP s hi hc hdg HT ai au af T).N, (epP s hi hc hdg HT ai au af T).E, (epP s hi hc hdg HT ai au af T).PP,
        (epP s hi hc hdg HT ai au af T).QQ, (epP s hi hc hdg HT ai au af T).DP, (epP s hi hc hdg HT ai au af T).DQ,
        (epP s hi hc hdg HT ai au af T).QI, (epP s hi hc hdg HT ai au af T).DIG D,
        (epP s hi hc hdg HT ai au af T).SALT, ⟨State.addr (stackArg s 20), (stackArg s 21).toNat * 8⟩,
        (epP s hi hc hdg HT ai au af T).HTAB, (epP s hi hc hdg HT ai au af T).TAB])
      [(epP s hi hc hdg HT ai au af T).OUT, (epP s hi hc hdg HT ai au af T).SCR] s 3440 := rfl

theorem epP_pre {s : State} (h32 : (stackArg s 21).toNat < 2 ^ 32)
    (hl : (stackArg s 21).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .r3).toNat (stackArg s 3).toNat
      (stackArg s 5).toNat) :
    PreP (epP s hi hc hdg HT ai au af T) :=
  ⟨rfl, rfl, h32, hl, rfl⟩

theorem in_of_preP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) {D : Nat}
    (hD : (stackArg s 13).toNat = D) (hHT : HT (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (epP s hi hc hdg HT ai au af T) (entered frameBytes s) ∧ PreP (epP s hi hc hdg HT ai au af T) := by
  sign_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA nS eS pS qS dpS dqS qiS
    dS slS sPr sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPr kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPr
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK prl key
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  obtain r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  obtain a7 : stackArg s 7 = stackArg s 3 := BitVec.eq_of_toNat_eq dpl
  obtain a11 : stackArg s 11 = stackArg s 3 := BitVec.eq_of_toNat_eq qil
  obtain a9 : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dql
  obtain a13 : stackArg s 13 = BitVec.ofNat 32 D := by
    apply BitVec.eq_of_toNat_eq; rw [hD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hD]; exact (stackArg s 13).isLt)]
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  rw [hD] at oD dS kD fD hrd
  obtain hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  obtain below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  obtain bP : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below).symm)
      (by show (stackArg s 3).toNat ≤ 2 ^ 64; omega_arith)
  obtain bQ : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 4)) (stackArg s 5).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kQ.sub_left below).symm)
      (by show (stackArg s 5).toNat ≤ 2 ^ 64; omega_arith)
  obtain wPre : ∀ n, n ≤ (stackArg s 21).toNat →
      Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 20)) n =
        Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 20)) n := fun n hn =>
    wordsAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (kPr.sub_left below).symm.sub_left (Region.sub_prefix (len' := (stackArg s 21).toNat * 8) (by omega_using [hn])))
      (by have := (stackArg s 21).isLt; omega_using [hn])
  obtain le : Spec.Rsa.precomputedWords (s.gpr .r3).toNat ≤ (stackArg s 21).toNat := by
    rw [prl, Spec.Rsa.privatePrecomputedWords]; omega_using []
  refine ⟨
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (stackArg s 15).isLt
      scl32 := (stackArg s 17).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      htabT := hHT
      tabT := hT
      A80 := (by decide : 80 ≤ 88)
      pxT := ⟨by rw [bP, bQ, wPre _ (Nat.le_refl _)]; exact key, by
        unfold Spec.Rsa.privatePrecomputedLeak; rw [wPre _ le]⟩ },
    epP_pre (stackArg s 21).isLt prl⟩
  rw [epP_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kPr, kTH, kT, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oPr, oTH, oT, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sPr, sTH, sT, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fD, fSl, fPr, fTH, fT, fO, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, epP, ep, r1]
    · rfl
    · simp [regArg, epP, ep]
  · intro i hi
    have : i < 22 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨
        i = 21) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp [epP, ep, a7, a9, a11, a13]

/-! ## The whole function -/

section
variable (mvs : List MVar) (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked_precomputed` over `v`. -/
abbrev signCodeP (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  signP (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)

/-- The contract, with those tables. -/
abbrev sspecP : Contract isa := specP (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)

variable {mvs vs}

theorem spec_tabP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 18).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 19).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13) := by
  sign_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA nS eS pS qS dpS dqS qiS
    dS slS sPr sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPr kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPr
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK prl key
  exact ⟨hheld, hheld2, hpw, fTH, fT, h⟩

theorem spec_spP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) : stackBytes ≤ s.sp.toNat := by
  sign_preP at h
  exact h.1

/-- The public parameters for the hash function's table of `w` and MGF1's of
`wg`, with their functions where `s'` has them. -/
abbrev epwP (s s' : State) (w : MVar) (wg : TVar) : EP :=
  epP s (s'.syms w.h.H.md.st.initN) (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w))
    (HTab w.h (MdHashTable.Arm.digName w) (MdHashTable.Arm.fnsOf mvs) (stackArg s 18) (s'.syms w.h.H.md.st.initN)
      (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w)))
    (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (RsaOaep.Arm.TabFacts wg.g.H (HashTable.Arm.fnsOf vs) (stackArg s 19) (s'.syms wg.g.H.initN)
      (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN))

theorem entered_stateP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) {s s' : State}
    (hs : (sspecP mvs vs).pre s) {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hhg : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (HashTable.Arm.tableOf wg)))
    (hsy : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s.syms n = s'.syms n) :
    Sy (S w.h (epwP (mvs := mvs) (vs := vs) s s' w wg)) (entered frameBytes s) (entered frameBytes s) ∧
      PreP (epwP (mvs := mvs) (vs := vs) s s' w wg) := by
  obtain ⟨-, -, hpw, hfit, hfitg, hdl⟩ := spec_tabP hs
  obtain hD := dl_of hfit hh hdl
  obtain hpwH := hpw.sublist (List.sublist_append_left _ _)
  obtain hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_spP hs)
  obtain ok := (in_of_preP (hi := 0) (hc := 0) (hdg := 0) (HT := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs hD trivial trivial).1.ok
  rw [epP_lay] at ok
  obtain hn := MdHashTable.Arm.mem_names hw
  obtain hng := Proof.HashTable.Arm.mem_names hwg
  obtain ht := MdHashTable.Arm.htab_entered ok hsp' (p := stackArg s 18) (by simp [epP, ep]) hfit hc hpwH hw hh
  obtain tf := Proof.HashTable.Arm.tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [epP, ep]) hfitg hcg hpwG
    hwg hhg
  rw [hsy _ (List.mem_append_left _ hn.1), hsy _ (List.mem_append_left _ hn.2.1),
    hsy _ (List.mem_append_left _ hn.2.2)] at ht
  rw [hsy _ (List.mem_append_right _ hng.1), hsy _ (List.mem_append_right _ hng.2.1),
    hsy _ (List.mem_append_right _ hng.2.2)] at tf
  obtain ⟨hi, hP⟩ := in_of_preP (hi := s'.syms w.h.H.md.st.initN) (hc := s'.syms w.h.H.md.compN)
    (hdg := s'.syms (MdHashTable.Arm.digName w)) (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN)
    (af := s'.syms wg.g.H.finN) hs hD ht tf
  exact ⟨⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩, hP⟩

/-- What the body needs of the tables of `w` and `wg`. -/
theorem tf_ofP {s s' : State} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs) :
    TF w.h wg.g (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (MdHashTable.Arm.digName w)
      (epwP (mvs := mvs) (vs := vs) s s' w wg) :=
  ⟨fun _ x => x, fun _ x => x, fne_of hw, gne_of hwg⟩

/-- Unfolds the contract's postcondition. -/
macro "sign_postP" : tactic => `(tactic| (
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]))

theorem code_okP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl)
    {s : State} (hs : (sspecP mvs vs).pre s) :
    WP isa (signCodeP mvs vs v) s fun t => abiPreserved s t ∧ (sspecP mvs vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, ⟨Tg, hTg, hhg⟩, -, hfit, hfitg, hdl⟩ := spec_tabP hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  obtain hidx := (MdHashTable.Arm.held_tableOf hfit hh).2.2.2
  obtain hidxg := (Proof.HashTable.Arm.held_tableOf hfitg hhg).2.1
  obtain ⟨st, hP⟩ := entered_stateP hc hcg hs hw hwg hh hhg (s' := s) fun _ _ => rfl
  have hin := st.1.1
  obtain hsp := spec_spP hs
  obtain hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  obtain hF : FrameOk frameBytes := by decide
  let P := epwP (mvs := mvs) (vs := vs) s s w wg
  obtain hb := (tab_vpP w.h wg.g P (tf_ofP hw hwg) w.shape w.mem hP v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (P.lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G P (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)
    (hQ := fun _ m₁ m₂ hf hres => by
      have fit := hin.ok.fits P.OUT (List.mem_append_right _ List.mem_cons_self)
      exact writtenOutcome_frame hf
        (released_apart (F := frameBytes) (A := 88) (C := 3440) (argv := (P.lay w.h.D).argv) (ro := (P.lay w.h.D).ro)
          (rw := (P.lay w.h.D).rw) hin.ok hsp' (R := P.OUT) (Or.inr (by simp)))
        (by change P.OUT.len ≤ 2 ^ 64; omega_using [fit]) hres)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 88) (C := 3440) (argv := (P.lay w.h.D).argv) (ro := (P.lay w.h.D).ro)
      (rw := (P.lay w.h.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sign_postP
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 18) = State.addr (stackArg s 18) from rfl,
      MdHashTable.Arm.hashAt_tableOf hfit hidx, Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl,
      Proof.HashTable.Arm.hashAt_tableOf hfitg hidxg, Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    obtain ro := fun {R : Region} (hR : R ∈ (P.lay w.h.D).ro) =>
      entered_ro (F := frameBytes) (A := 88) (C := 3440) (argv := (P.lay w.h.D).argv) (rw := (P.lay w.h.D).rw) hin.ok
        hsp' hR
    obtain hP' : pB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
      ro (R := P.PP) (by simp)
    obtain hQ : qB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
      ro (R := P.QQ) (by simp)
    obtain hDP : dpB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        (stackArg s 3).toNat := ro (R := P.DP) (by simp)
    obtain hDQ : dqB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8))
        (stackArg s 5).toNat := ro (R := P.DQ) (by simp)
    obtain hQI : qiB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10))
        (stackArg s 3).toNat := ro (R := P.QI) (by simp)
    obtain hDg : digB w.h P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 12)) w.h.D :=
      ro (R := P.DIG w.h.D) (by simp)
    obtain hS : saltB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 14))
        (stackArg s 15).toNat := ro (R := P.SALT) (by simp)
    unfold Res at res
    rw [hP', hQ, hDP, hDQ, hQI, hDg, hS] at res
    rw [w.h.glen]
    exact res

theorem code_ctP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (sspecP mvs vs).pre (sspecP mvs vs).pub (signCodeP mvs vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, ⟨Tg, hTg, hhg₁⟩, -, -, -, -⟩ := spec_tabP h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, htabg, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19, a20, a21⟩ := hp
  obtain hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  obtain hhg₂ := (htabg _ _ rfl rfl _ hTg).mp hhg₁
  obtain hsy' : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by
      rcases List.mem_append.mp hn with e | e
      · exact List.mem_append_left _ e
      · exact List.mem_append_right _ (List.mem_append_left _ e))).symm
  obtain hep : epwP (mvs := mvs) (vs := vs) s₁ s₁ w wg = epwP (mvs := mvs) (vs := vs) s₂ s₁ w wg := by
    obtain ⟨hl1, hleak⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3, a1])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl1) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3])
    simp only [epP, ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a8, a10, a12, a14, a15, a16, a17, a18, a19, a20, a21]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [a20, h3] at hleak
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
      show State.addr (stackArg s₂ 20) = BitVec.setWidth 64 (stackArg s₂ 20) from rfl, hleak]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_spP h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨st₁, hP⟩ := entered_stateP hc hcg h₁ hw hwg hh₁ hhg₁ (s' := s₁) (fun _ _ => rfl)
  refine (tab_vpP w.h wg.g (epwP (mvs := mvs) (vs := vs) s₁ s₁ w wg) (tf_ofP hw hwg) w.shape w.mem hP v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, st₁, by rw [hep]; exact (entered_stateP hc hcg h₂ hw hwg hh₂ hhg₂ (s' := s₁) hsy').1⟩

/-- `vg_rsa_pss_sign_precomputed`, calling `vg_rsa_private_checked_precomputed` over `v`, with the
hash function any of the tables of `MdHash` of `mvs` and MGF1's any of the
tables of `MdHash` of `vs`, meets its contract (satisfiable, `SgSat.lean`). -/
theorem sign_verifiedP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs)
    (hsat : ∃ s, (sspecP mvs vs).pre s) (v : Proof.Rsa.Arm.CrtImpl) : Verified target (signCodeP mvs vs v) (sspecP mvs vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_okP hc hcg v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ctP hc hcg v, hsat⟩

end

end VG.Proof.RsaPss.Arm.Sg
end

end

/-! ### `RsaPss.Arm.SgSat`, which only this module used -/

section

/-!
# RSASSA-PSS signing on ARMv7 with the tables: the contract is satisfiable

A state with the table of `MdHash` of `w` at `0x300000` and the table of
`Hash` of `wg` at `0x300100` (`withTabs`, the stack arguments' values), and
the tables' functions at distinct addresses (`symsOf32`), and the arguments
of a 512-bit key, a digest of `w`'s length and an empty salt: `sign_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct readW_sep32)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- The words `ws` written from `p`, 32 bits each. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p (w.setWidth 32)) (p + 4) ws

theorem add4_toNat {p : Addr} (h : p.toNat + 4 < 2 ^ 64) : (p + 4).toNat = p.toNat + 4 := by
  rw [BitVec.toNat_add, show (4 : Addr).toNat = 4 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 4 ≤ p.toNat ∨ p.toNat + 4 * ws.length ≤ a.toNat) → p.toNat + 4 * ws.length < 2 ^ 64 →
    a.toNat + 4 ≤ 2 ^ 64 → (putWs m p ws).readW a 32 = m.readW a 32
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h4 := add4_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_out (by rw [h4]; omega_using [h]) (by rw [h4]; omega_using [hp]) ha, readW_sep32 (by omega_using [h]) ha (by omega_using [hp])]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 4 * ws.length < 2 ^ 64 →
    Abi.tableHeld 32 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h4 := add4_toNat (p := p) (by omega_using [hp])
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (32 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h4])) (by rw [h4]; omega_using [hp]) (by omega_using [hp]), Mem.readW_writeW_self32]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p (w.setWidth 32)) (p := p + 4) (ws := ws) (by rw [h4]; omega_using [hp]) i
        (by simp at hi; omega_using [hi])
      rw [show p + BitVec.ofNat 64 (32 / 8 * (i + 1)) = p + 4 + BitVec.ofNat 64 (32 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega_using []]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf32 ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (fun n => (symsOf32 ns n).setWidth 64) ++ T.data

/-- The names of the tables' functions. -/
def allNames (mvs : List MVar) (vs : List TVar) : List String :=
  MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs

/-- The memory `m` with the table of `MdHash` of `w` at `0x300000` and the
table of `MdHash` of `wg` at `0x300100`, and `m` itself below `0x300000`. -/
def tabMem (m : Mem) (mvs : List MVar) (vs : List TVar) (w : MVar) (wg : TVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w))) 0x300100
    (tw (allNames mvs vs) (HashTable.Arm.tableOf wg)) a

/-- A state with `s`'s registers and regions, those tables, and the tables'
functions at distinct addresses. -/
def withTabs (s : State) (mvs : List MVar) (vs : List TVar) (w : MVar) (wg : TVar) : State :=
  { s with mem := tabMem s.mem mvs vs w wg, syms := symsOf32 (allNames mvs vs) }

variable {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar}

/-- Below `0x300000`, a word as in `s`. -/
theorem withTabs_below (s : State) {a : Addr} (ha : a.toNat + 4 ≤ 0x300000) :
    (withTabs s mvs vs w wg).mem.readW a 32 = s.mem.readW a 32 := by
  refine Mem.readW_congr fun i hi => ?_
  have : (a + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [ha, hi]
  simp only [withTabs, tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- A stack argument below `0x300000`, as in `s`. -/
theorem withTabs_arg (s : State) {j : Nat} (hj : (stackArgAddr s j).toNat + 4 ≤ 0x300000) :
    stackArg (withTabs s mvs vs w wg) j = stackArg s j :=
  show (withTabs s mvs vs w wg).mem.readW (stackArgAddr s j) 32 = s.mem.readW (stackArgAddr s j) 32 from
    withTabs_below s hj

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 4 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 32 (putWs (putWs m 0x300000 (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w))) 0x300100
      (tw (allNames mvs vs) (HashTable.Arm.tableOf wg))) p ws) :
    Abi.tableHeld 32 (tabMem m mvs vs w wg) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (32 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hp, hl, hi, hk]
  have hb : Nat.blt (p + BitVec.ofNat 64 (32 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem tw_words (s : State) (hs : s.syms = symsOf32 (allNames mvs vs)) (T : FnTable) :
    FnTable.words isa s T = tw (allNames mvs vs) T := by
  simp only [FnTable.words, tw, hs]

theorem withTabs_heldH (s : State) :
    Abi.tableHeld 32 (withTabs s mvs vs w wg).mem 0x300000
      (FnTable.words isa (withTabs s mvs vs w wg) (MdHashTable.Arm.tableOf w)) := by
  have hl : (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.Arm.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  rw [tw_words _ rfl]
  refine tabMem_above (by decide) (by rw [hl]; decide) fun i hi => ?_
  rw [hl] at hi
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, c1, c2, Nat.reduceDiv]; omega_using [hi]))
    (by simp [tw, HashTable.Arm.tableOf, MdHashTable.Arm.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, c1, Nat.reduceDiv]; omega_using [])]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi)

theorem withTabs_heldG (s : State) :
    Abi.tableHeld 32 (withTabs s mvs vs w wg).mem 0x300100
      (FnTable.words isa (withTabs s mvs vs w wg) (HashTable.Arm.tableOf wg)) := by
  rw [tw_words _ rfl]
  exact tabMem_above (by decide) (by simp [tw, HashTable.Arm.tableOf, MdHashTable.Arm.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.Arm.tableOf, MdHashTable.Arm.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]))

namespace Sg

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `D` bytes,
an empty salt, the stack arguments at `0x8000`, and the tables' addresses
`0x300000` and `0x300100`. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 1 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 1 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 1 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 1 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 1 else
    if a = 0x8031 then 0x30 else
    if a = 0x8034 then BitVec.ofNat 8 D else
    if a = 0x8039 then 0x36 else
    if a = 0x8042 then 1 else
    if a = 0x8044 then 0x20 else
    if a = 0x8045 then 8 else
    if a = 0x804a then 0x30 else
    if a = 0x804d then 1 else
    if a = 0x804e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩, ⟨0x8000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- Its stack arguments. -/
def satArgs (D : Nat) : Nat → BitVec 32
  | 0 => 0x2100 | 1 => 1 | 2 => 0x3100 | 3 => 1 | 4 => 0x3200 | 5 => 1 | 6 => 0x3300 | 7 => 1
  | 8 => 0x3400 | 9 => 1 | 10 => 0x3500 | 11 => 1 | 12 => 0x3000 | 13 => BitVec.ofNat 32 D | 14 => 0x3600
  | 15 => 0 | 16 => 0x10000 | 17 => 0x820 | 18 => 0x300000 | _ => 0x300100

theorem sat_args (D : Nat) : ∀ j < 20, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by
  show ∀ j < 20, (stackArgAddr (satState 0) j).toNat + 4 ≤ 0x300000
  decide

/-- A region within `⟨p, 64⟩`, apart from what that is apart from. -/
theorem dig_disj {A : Region} {p : Addr} {D : Nat} (hD : D ≤ 64) (h : A.Disjoint ⟨p, 64⟩) : A.Disjoint ⟨p, D⟩ :=
  h.sub_right fun a ha => by simp only [Region.Contains] at ha ⊢; omega_using [hD, ha]

theorem sat_b16 : ∀ j < 20, stackArg (satState 16) j = satArgs 16 j := by decide
theorem sat_b20 : ∀ j < 20, stackArg (satState 20) j = satArgs 20 j := by decide
theorem sat_b28 : ∀ j < 20, stackArg (satState 28) j = satArgs 28 j := by decide
theorem sat_b32 : ∀ j < 20, stackArg (satState 32) j = satArgs 32 j := by decide
theorem sat_b48 : ∀ j < 20, stackArg (satState 48) j = satArgs 48 j := by decide
theorem sat_b64 : ∀ j < 20, stackArg (satState 64) j = satArgs 64 j := by decide

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satState D).gpr) (hsp : s.sp = (satState D).sp) (ha : ∀ j < 20, stackArg s j = satArgs D j)
    (hrd : s.rd = (satState D).rd) (hwr : s.wr = (satState D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D)) :
    (spec hs ts).pre s := by
  have g0 : s.gpr .r0 = 0x1000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2000 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 64 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr,
    satArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega_using [hD])
    | skip

theorem sign_sat_of {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 20, stackArg (satState D) j = satArgs D j) :
    (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre (withTabs (satState D) mvs vs w wg) :=
  sign_pre_of hD rfl rfl (fun j hj => (withTabs_arg _ (sat_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satState D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), hlen]

/-- Signing's contract, with the tables of `mvs` and `vs`, is satisfiable. -/
theorem sign_sat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b16⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b20⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b28⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b32⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b48⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b64⟩

/-! ## Signing with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `satStateP D`: the key `keyMem` holds, a digest of
`D` bytes, an empty salt, a working space of 2080 words, the tables at
`0x300000` and `0x300100`, and `pre` at `0x4800`. -/
def satArgsP (D : Nat) : List Nat :=
  [0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3000, D, 0x3600, 0, 0x10000, 0x820,
    0x300000, 0x300100, 0x4800, 24]

/-- The memory of `satStateP D`: the stack arguments from `0x8000`, and the
key. -/
def satMemP (D : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x8058 then
    BitVec.ofNat 8 ((satArgsP D).getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed signing's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def satStateP (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMemP D
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩, ⟨0x8000, 88⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

theorem sat_argsP (D : Nat) : ∀ j < 22, (stackArgAddr (satStateP D) j).toNat + 4 ≤ 0x300000 := fun j hj => by
  have c0 : (0x8000 : BitVec 32).toNat = 0x8000 := rfl
  simp only [stackArgAddr, satStateP, State.addr, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, c0]
  omega_using [hj]

theorem satP_b16 : ∀ j < 22, stackArg (satStateP 16) j = BitVec.ofNat 32 ((satArgsP 16).getD j 0) := by decide
theorem satP_b20 : ∀ j < 22, stackArg (satStateP 20) j = BitVec.ofNat 32 ((satArgsP 20).getD j 0) := by decide
theorem satP_b28 : ∀ j < 22, stackArg (satStateP 28) j = BitVec.ofNat 32 ((satArgsP 28).getD j 0) := by decide
theorem satP_b32 : ∀ j < 22, stackArg (satStateP 32) j = BitVec.ofNat 32 ((satArgsP 32).getD j 0) := by decide
theorem satP_b48 : ∀ j < 22, stackArg (satStateP 48) j = BitVec.ofNat 32 ((satArgsP 48).getD j 0) := by decide
theorem satP_b64 : ∀ j < 22, stackArg (satStateP 64) j = BitVec.ofNat 32 ((satArgsP 64).getD j 0) := by decide

/-- The key, in a state with the tables. -/
theorem satP_key (D : Nat) {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs (satStateP D) mvs vs w wg).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs (satStateP D) mvs vs w wg).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs (satStateP D) mvs vs w wg).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTabs (satStateP D) mvs vs w wg).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h1 : Nat.blt a.toNat 0x300000 = true := Nat.blt_eq.mpr (by omega_using [hk])
    have h2 : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x8058) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show (bif _ then _ else _) = _
    rw [h1, Bool.cond_true]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

/-- The precomputed signing's precondition, from the facts of a state. -/
theorem sign_pre_ofP {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satStateP D).gpr) (hsp : s.sp = (satStateP D).sp)
    (ha : ∀ j < 22, stackArg s j = BitVec.ofNat 32 ((satArgsP D).getD j 0))
    (hrd : s.rd = (satStateP D).rd) (hwr : s.wr = (satStateP D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D))
    (hkey : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (specP hs ts).pre s := by
  have g0 : s.gpr .r0 = 0x1000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2000 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 64 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide),
    ha 21 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr, satArgsP]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact hkey)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega_using [hD])

theorem sign_sat_ofP {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 22, stackArg (satStateP D) j = BitVec.ofNat 32 ((satArgsP D).getD j 0)) :
    (specP (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre (withTabs (satStateP D) mvs vs w wg) :=
  sign_pre_ofP hD rfl rfl (fun j hj => (withTabs_arg _ (sat_argsP D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) (fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satStateP D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), hlen]) (satP_key D)

/-- The precomputed signing's contract, with the tables of `mvs` and `vs`, is
satisfiable. -/
theorem sign_satP {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (specP (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b16⟩
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b20⟩
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b28⟩
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b32⟩
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b48⟩
  · exact ⟨_, sign_sat_ofP hw hwg hl (by decide) e satP_b64⟩

end Sg

end VG.Proof.RsaPss.Arm

end

end

/-! ### `RsaPss.Arm.VfSat`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7 with the tables: the contract is satisfiable

A state with the table of `MdHash` of `w` at `0x300000` and the table of
`Hash` of `wg` at `0x300100` (signing's `withTabs`), and the arguments of a
64-byte modulus, a one-byte `e`, a digest of `w`'s length, a 64-byte
signature, the working space it needs and the precomputed values' 16 words,
the stack arguments at `0x8000`: `verify_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- The state but for the tables, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x2100 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then BitVec.ofNat 8 D else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x40 else
    if a = 0x801a then 1 else
    if a = 0x801c then 0x20 else
    if a = 0x801d then 8 else
    if a = 0x8021 then 0x70 else
    if a = 0x8024 then 0x10 else
    if a = 0x802a then 0x30 else
    if a = 0x802d then 1 else
    if a = 0x802e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩,
    ⟨0x8000, 48⟩]
  wr := [⟨0x10000, 2080 * 8⟩]

/-- Its stack arguments. -/
def satArgs (D : Nat) : Nat → BitVec 32
  | 0 => 0x3000 | 1 => BitVec.ofNat 32 D | 2 => 0x3100 | 3 => 64 | 4 => 0 | 5 => 0 | 6 => 0x10000 | 7 => 0x820
  | 8 => 0x7000 | 9 => 16 | 10 => 0x300000 | _ => 0x300100

theorem sat_args (D : Nat) : ∀ j < 12, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by
  show ∀ j < 12, (stackArgAddr (satState 0) j).toNat + 4 ≤ 0x300000
  decide

theorem sat_b16 : ∀ j < 12, stackArg (satState 16) j = satArgs 16 j := by decide
theorem sat_b20 : ∀ j < 12, stackArg (satState 20) j = satArgs 20 j := by decide
theorem sat_b28 : ∀ j < 12, stackArg (satState 28) j = satArgs 28 j := by decide
theorem sat_b32 : ∀ j < 12, stackArg (satState 32) j = satArgs 32 j := by decide
theorem sat_b48 : ∀ j < 12, stackArg (satState 48) j = satArgs 48 j := by decide
theorem sat_b64 : ∀ j < 12, stackArg (satState 64) j = satArgs 64 j := by decide

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satState D).gpr) (hsp : s.sp = (satState D).sp) (ha : ∀ j < 12, stackArg s j = satArgs D j)
    (hrd : s.rd = (satState D).rd) (hwr : s.wr = (satState D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D)) :
    (spec hs ts).pre s := by
  have g0 : s.gpr .r0 = 0x2000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2100 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 1 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr, satArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (simp only [Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords,
        Spec.Rsa.modulusWords]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact Sg.dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (Sg.dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega_using [hD])
    | skip

theorem verify_sat_of {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 12, stackArg (satState D) j = satArgs D j) :
    (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre (withTabs (satState D) mvs vs w wg) :=
  verify_pre_of hD rfl rfl (fun j hj => (withTabs_arg _ (sat_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satState D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), hlen]

/-- Verification's contract, with the tables of `mvs` and `vs`, is satisfiable. -/
theorem verify_sat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b16⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b20⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b28⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b32⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b48⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b64⟩

end VG.Proof.RsaPss.Arm.Vf

end

end


/-!
# RSASSA-PSS on ARMv7: the instances emitted

What the registrations check of the hash functions whose tables a function
takes (`OK`), and the instances' proofs against the contracts the
registrations state, with the hash function any of the tables of `MdHash`
and MGF1's any of the tables of `MdHash`: signing (`sign_ok`) and
verification (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- What the registrations check of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one of each kind. -/
def OK (mvs : List MVar) (vs : List TVar) : Prop :=
  MdHashTable.Arm.Coh mvs ∧ HashTable.Arm.Coh vs ∧ (allNames mvs vs).length < 2 ^ 24 ∧ mvs ≠ [] ∧ vs ≠ []

instance (mvs : List MVar) (vs : List TVar) : Decidable (OK mvs vs) := by unfold OK; infer_instance

/-- `vg_rsa_pss_sign`, with the tables of `mvs` and `vs` and the private-key
operation over `v`. -/
theorem sign_ok {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Sg.signCode mvs vs v) (Sg.sspec mvs vs) :=
  Sg.sign_verified hok.1 hok.2.1 (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
    let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; Sg.sign_sat hw hwg hok.2.2.1) v

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `mvs` and `vs` and
`vg_rsa_private_checked_precomputed` over `v`. -/
theorem signP_ok {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Sg.signCodeP mvs vs v) (Sg.sspecP mvs vs) :=
  Sg.sign_verifiedP hok.1 hok.2.1 (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
    let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; Sg.sign_satP hw hwg hok.2.2.1) v

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `mvs` and `vs`,
calling `c`. -/
theorem verify_ok {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Vf.verifyCode mvs vs c) (Vf.vspec mvs vs) :=
  Vf.verify_verified hok.1 hok.2.1 (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
    let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; Vf.verify_sat hw hwg hok.2.2.1) c

end VG.Proof.RsaPss.Arm
