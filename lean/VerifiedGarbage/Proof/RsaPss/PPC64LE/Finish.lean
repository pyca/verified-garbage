module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix

/-!
# RSASSA-PSS verification on PPC64LE: `H'` and the result

Untrusted: everything here is checked by Lean. `fixed_ok` and `any_ok`: the
two branches of `finish`, from the state after the checks of `DB`: the
result is 1 exactly when the accumulator is zero and `H` is the hash of
`M' = 0⁸ ‖ mHash ‖ salt` (`mFix`: the last `salt_len` bytes of `DB`;
`mAny`: the `sl` bytes after `pos`), as views of `EM`'s place.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `M'` for a given salt length `sl`: the last `sl` bytes of `DB` (at `lo`,
`dbLen` bytes, in the view `V`). -/
def mFix (V : Nat → Byte) (mh : List Byte) (lN dN sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => V (lN + dN - sl + j)

/-- `M'` for any salt length: the `sl` bytes of `DB` after `pos`. -/
def mAny (V : Nat → Byte) (mh : List Byte) (lN dN pos sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => if j + (pos + 1) < dN then V (lN + (j + (pos + 1))) else 0

/-- The `n` bytes of `M'` at `oY`. -/
abbrev mB (m : Mem) (S : Addr) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (off S oY) n

/-- The bytes of `M'` at `oY`, from their view. -/
theorem mB_eq {m : Mem} {S : Addr} {D n : Nat} {mh rest : List Byte} (hmh : mh.length = D)
    (hr : rest.length = n) (h : ∀ i < 8 + D + n, view m S (oY + i) = (List.replicate 8 0 ++ mh ++ rest).getD i 0) :
    mB m S (8 + D + n) = List.replicate 8 0 ++ mh ++ rest := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hmh, hr]; omega_arith)
  intro i h₁ h₂
  have hi : i < 8 + D + n := by simpa [Spec.Sha256.bytesAt] using h₁
  have := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at this
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  rw [← this, view, ← off_off]

theorem getD_m3 {mh rest : List Byte} {D : Nat} (hmh : mh.length = D) (i : Nat) :
    (List.replicate 8 0 ++ mh ++ rest).getD i 0 =
      if i < 8 then 0 else if i < 8 + D then mh.getD (i - 8) 0 else rest.getD (i - 8 - D) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases h₁ : i < 8
  · rw [ifp h₁, List.getElem?_append_left (by simp; omega_arith), List.getElem?_replicate, ifp h₁]; rfl
  · rw [ifn h₁, List.getElem?_append_right (by simp; omega_arith), List.length_replicate]
    by_cases h₂ : i < 8 + D
    · rw [ifp h₂, List.getElem?_append_left (by omega_arith)]
    · rw [ifn h₂, List.getElem?_append_right (by omega_arith), hmh, Nat.sub_sub]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {p : Addr} (T : MdTabS H cn cc dn dc f hArg Sp s p)
include L hH T

theorem fixed_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) (hsl : (stackArg s 0).toNat + 1 ≤ dN)
    (ha : (t.gpr .r24).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H 8) (.seq (copySalt H) (.seq (hashFixed H f hArg) (cmpH H oDig)))) t fun t' =>
      Base Sp (vP D) s t' ∧ t'.gpr .r3 = if t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN (stackArg s 0).toNat)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  generalize hS : (stackArg s 0).toNat = sl at hsl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 8) (Nat.le_refl _) (by decide) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (salt_ok L hD b₁ (by rw [hS]; exact hsl)) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  rw [hS] at v₂
  refine WP.seq (WP.mono (hashFixed_ok F hH T hD b₂ (y₂.trans (y₁.trans sy)) (by rw [hS]; omega_arith))
    fun t₃ ⟨⟨b₃, g₃, s₃, d₃⟩, _⟩ => ?_)
  rw [hS] at d₃
  have g24 : t₃.gpr .r24 = t.gpr .r24 := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₃ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  have vH : ∀ i < D, view t₃.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [s₃ _ (by omega_arith) (fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> simp only <;> omega_arith),
      v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  have hM : mB t₂.mem (Sp s) (8 + D + sl) = mFix (view t.mem (Sp s)) (mh D s) lN dN sl := by
    refine mB_eq (by simp [Spec.Rsa.bytesAt]) (by simp) fun i hi => ?_
    rw [getD_m3 (D := D) (by simp [Spec.Rsa.bytesAt]), v₂ _ (by omega_arith)]
    by_cases h₁ : i < 8
    · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega_arith), v₁ _ (by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 8 by omega_arith), ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega_arith), v₁ _ (by omega_arith),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega_arith), ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega_arith]
      · rw [ifp (show oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl by omega_arith), v₁ _ (by omega_arith),
          ifn (show ¬(oY + 8 ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8 + D) by omega_arith),
          ifn (show ¬(oY ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8) by omega_arith), ifn h₁, ifn h₂]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i - 8 - D < sl by omega_arith),
          Option.map_some, Option.getD_some]
        congr 2; omega_arith
  have vD : ∀ i < D, view t₃.mem (Sp s) (oDig + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0 := fun i hi => by
    have d₃' := d₃
    rw [show Spec.Sha256.bytesAt t₂.mem (off (Sp s) oY) (8 + D + sl) = _ from hM] at d₃'
    have := congrArg (·.getD i 0) d₃'
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < H.FD by have := hH.hDF; omega_arith), Option.map_some, Option.getD_some] at this
    rw [view, ← off_off, this, hGh, hH.hashTake, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega_arith), ← List.getD_eq_getElem?_getD]
  by_cases e : t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

theorem any_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
    (hN : H.N = P.N) (hB : H.B = P.B) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {pos sl : Nat} (h8 : t.gpr .r8 = BitVec.ofNat 64 pos)
    (hp : pos < dN) (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) (hsl : sl + pos + 1 = dN)
    (ha : (t.gpr .r24).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H 2048) (.seq (copyDb H) (.seq (shift H) (.seq (ctHash H P f hArg) (cmpH H oDig))))) t
      fun t' => Base Sp (vP D) s t' ∧ t'.gpr .r3 = if t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 2048) (by decide) (Nat.le_refl _) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (copyDb_ok L hD b₁) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  refine WP.seq (WP.mono_syms (shift_ok L hD b₂ (pos := pos) (by rw [g₂ _ (by decide), g₁ _ (by decide), h8]) hp)
    fun t₃ ⟨b₃, k₃, v₃⟩ y₃ => ?_)
  let b := oY + 8 + D
  let msg := mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl
  have hml : msg.length = 8 + D + sl := by simp [msg, mAny, Spec.Rsa.bytesAt]; omega_arith
  have w₂ : ∀ o < oRsa, ¬(b ≤ o ∧ o < b + dN) → ¬(oY ≤ o ∧ o < oY + 2048) → view t₂.mem (Sp s) o = view t.mem (Sp s) o :=
    fun o ho h₁ h₂ => by rw [v₂ o ho, ifn h₁, v₁ o ho, ifn (by omega_arith), ifn h₂]
  have hz : ∀ x, dN ≤ x → x < dN + 2 ^ 9 → view t₂.mem (Sp s) (b + x) = 0 := fun x h₁ h₂ => by
    have : (2 : Nat) ^ 9 = 512 := rfl
    rw [v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifp (by omega_arith)]
  have hMl : (mh D s).length = D := by simp [Spec.Rsa.bytesAt]
  have hYv : ∀ i < 2048, view t₃.mem (Sp s) (oY + i) = msg.getD i 0 := by
    intro i hi
    show _ = (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl).getD i 0
    unfold mAny
    rw [v₃ _ (by omega_arith)]
    by_cases h₁ : i < 8
    · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_arith), getD_m3 hMl, ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega_arith), getD_m3 hMl, ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega_arith]
      · rw [getD_m3 hMl, ifn h₁, ifn h₂]
        by_cases h₃ : i < 8 + D + dN
        · rw [show oY + i = b + (i - 8 - D) by omega_arith, shV_eq _ (by omega_arith) hz (by omega_arith)]
          by_cases h₄ : i - 8 - D < sl
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h₄, Option.map_some,
              Option.getD_some]
            by_cases e : i - 8 - D + (pos + 1) < dN
            · rw [ifp e, ifp e, v₂ _ (by omega_arith), ifp (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith),
                ifn (by omega_arith)]
              congr 1; omega_arith
            · rw [ifn e, ifn e]
          · rw [ifn (by omega_arith), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega_arith)]; rfl
        · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
            ifn (by omega_arith), ifp (by omega_arith), List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp; omega_arith)]; rfl
  refine WP.seq (WP.mono (ctHash_ok L hH T ok hl hD hN hB b₃ (y₃.trans (y₂.trans (y₁.trans sy))) (sl := sl)
    (by rw [k₃.get .r25, g₂ _ (by decide), g₁ _ (by decide), h25]) (by omega_arith) hml hYv)
    fun t₄ ⟨⟨b₄, g24₄, mem₄, d₄⟩, _⟩ => ?_)
  have g24 : t₄.gpr .r24 = t.gpr .r24 := by rw [g24₄, k₃.get .r24, g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₄ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  have vH : ∀ i < D, view t₄.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [mem₄ _ (by omega_arith), v₃ _ (by omega_arith), shV_out _ _ _ _ _ _ (by omega_arith),
      w₂ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  have vD : ∀ i < D, view t₄.mem (Sp s) (oDig + i) = (Gs.hash msg).getD i 0 := fun i hi => by rw [d₄ i hi, hGh]
  by_cases e : t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) = (Gs.hash msg).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE
