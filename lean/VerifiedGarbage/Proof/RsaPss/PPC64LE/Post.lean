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
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPss.PPC64LE.Finish`, which only this module used -/

section

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
  obtain hi : i < 8 + D + n := by simpa [Spec.Sha256.bytesAt] using h₁
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
  obtain Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  generalize hS : (stackArg s 0).toNat = sl at hsl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 8) (Nat.le_refl _) (by decide) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (salt_ok L hD b₁ (by rw [hS]; exact hsl)) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  rw [hS] at v₂
  refine WP.seq (WP.mono (hashFixed_ok F hH T hD b₂ (y₂.trans (y₁.trans sy)) (by rw [hS]; omega_arith))
    fun t₃ ⟨⟨b₃, g₃, s₃, d₃⟩, _⟩ => ?_)
  rw [hS] at d₃
  obtain g24 : t₃.gpr .r24 = t.gpr .r24 := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₃ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  obtain vH : ∀ i < D, view t₃.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [s₃ _ (by omega_arith) (fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> simp only <;> omega_arith),
      v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  obtain hM : mB t₂.mem (Sp s) (8 + D + sl) = mFix (view t.mem (Sp s)) (mh D s) lN dN sl := by
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
  obtain vD : ∀ i < D, view t₃.mem (Sp s) (oDig + i) =
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
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 2048) (by decide) (Nat.le_refl _) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (copyDb_ok L hD b₁) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  refine WP.seq (WP.mono_syms (shift_ok L hD b₂ (pos := pos) (by rw [g₂ _ (by decide), g₁ _ (by decide), h8]) hp)
    fun t₃ ⟨b₃, k₃, v₃⟩ y₃ => ?_)
  let b := oY + 8 + D
  let msg := mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl
  obtain hml : msg.length = 8 + D + sl := by simp [msg, mAny, Spec.Rsa.bytesAt]; omega_arith
  obtain w₂ : ∀ o < oRsa, ¬(b ≤ o ∧ o < b + dN) → ¬(oY ≤ o ∧ o < oY + 2048) → view t₂.mem (Sp s) o = view t.mem (Sp s) o :=
    fun o ho h₁ h₂ => by rw [v₂ o ho, ifn h₁, v₁ o ho, ifn (by omega_arith), ifn h₂]
  obtain hz : ∀ x, dN ≤ x → x < dN + 2 ^ 9 → view t₂.mem (Sp s) (b + x) = 0 := fun x h₁ h₂ => by
    have : (2 : Nat) ^ 9 = 512 := rfl
    rw [v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifp (by omega_arith)]
  obtain hMl : (mh D s).length = D := by simp [Spec.Rsa.bytesAt]
  obtain hYv : ∀ i < 2048, view t₃.mem (Sp s) (oY + i) = msg.getD i 0 := by
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
  obtain g24 : t₄.gpr .r24 = t.gpr .r24 := by rw [g24₄, k₃.get .r24, g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₄ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  obtain vH : ∀ i < D, view t₄.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [mem₄ _ (by omega_arith), v₃ _ (by omega_arith), shV_out _ _ _ _ _ _ (by omega_arith),
      w₂ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  obtain vD : ∀ i < D, view t₄.mem (Sp s) (oDig + i) = (Gs.hash msg).getD i 0 := fun i hi => by rw [d₄ i hi, hGh]
  by_cases e : t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) = (Gs.hash msg).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Unmask`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: `DB`

Untrusted: everything here is checked by Lean. `unmask_ok`: `dbArgs` (`dbArgs_ok`), MGF1
through its table (`mgfXorT_ok`, shared with RSAES-OAEP encryption) and `clearTop` (`clearTop_ok`) leave `DB` in
`EM`'s place: `maskedDB` XORed with MGF1 of `H`, its first byte ANDed with
`c` (`dbV`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa Fns mgfXorT)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs MFit TabS mgfXorT_ok)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_add wp_mov wp_and wp_lbz wp_stb wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `DB` in `EM`'s place, from its view `V` before unmasking. -/
def dbV (Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (lN dN D : Nat) (c : Byte) (o : Nat) : Byte :=
  let W := mixV V (Spec.Mgf1.mgf1 Gs (srcB V (lN + dN) D) dN) lN dN
  if o = lN then W o &&& c else W o

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- MGF1's arguments for unmasking `DB`: `H` after it as the seed. -/
theorem dbArgs_ok {H : Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block (dbArgs H)) t fun t' => Base Sp (vP D) s t' ∧ Only [.r26, .r27, .r24, .r25] t t' ∧
      t'.gpr .r24 = off (Sp s) (lN + dN) ∧ t'.gpr .r25 = BitVec.ofNat 64 D ∧ t'.gpr .r26 = off (Sp s) lN ∧
      t'.gpr .r27 = BitVec.ofNat 64 dN := by
  have F := L.F
  have hD64 := L.D64
  subst hD
  refine wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_nil ?_
  obtain k₄ : Only [.r26, .r27, .r24, .r25] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  obtain a26 : t₁.gpr .r26 = off (Sp s) lN := by rw [e₁, h.r14, h.plo, L.hlo]
  exact ⟨h.only F k₄, k₄,
    by rw [o₄.get .r24, e₃, o₂.get .r26, a26, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb]; exact off_off _ _ _,
    by rw [e₄], by rw [o₄.get .r26, o₃.get .r26, o₂.get .r26, a26],
    by rw [o₄.get .r27, o₃.get .r27, e₂, o₁.get .r21, h.pdb, L.hdb]⟩

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block clearTop) t fun w => Base Sp (vP D) s w ∧ Keep [.r4, .r5] t w ∧
      ∀ o < oSt, view w.mem (Sp s) o = if o = lN then view t.mem (Sp s) lN &&& c else view t.mem (Sp s) o := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hl := L.l1
  obtain a6 : ∀ {u : State}, Only [.r4] t u → u.gpr .r4 = t.gpr .r14 + t.gpr .r17 → u.gpr .r4 = off (Sp s) lN :=
    fun o e => by rw [e, h.r14, h.plo, L.hlo]
  refine wp_add fun t₆ o₆ e₆ => ?_
  refine wp_lbz (a := off (Sp s) lN) (by rw [a6 o₆ e₆, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_arith) _) fun t₇ o₇ e₇ => ?_
  refine wp_and fun t₈ o₈ e₈ => wp_stb (a := off (Sp s) lN) (by rw [o₈.get .r4, o₇.get .r4, a6 o₆ e₆,
    BitVec.add_zero]) (by rw [o₈.wr, o₇.wr, o₆.wr, h.wr]; exact sc_inW F (by unfold oRsa; omega_arith)) fun w mw => ?_
  obtain k₈ : Only [.r4, .r5] t t₈ := (o₆.trans (o₇.trans o₈)).mono
  obtain hK : Keep [.r4, .r5] t w := (k₈.keep.trans mw.keep).mono
  obtain hb : (t₈.gpr .r5).setWidth 8 = view t.mem (Sp s) lN &&& c := by
    rw [e₈, e₇, o₇.get .r18, o₆.get .r18, h.pc, L.hc, o₆.mem]
    simp only [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
    rfl
  obtain hm : w.mem = t.mem.writeW (off (Sp s) lN) (view t.mem (Sp s) lN &&& c) := by
    rw [mw.mem, hb, k₈.mem]
  refine wp_nil ⟨h.keep F hK (R := [⟨off (Sp s) lN, 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega_arith))), hK, fun o ho => ?_⟩
  rw [hm, view_w8 _ _ (by unfold oRsa; omega_arith) (by unfold oSt oRsa at *; omega_arith)]

theorem unmask_ok {H : Hash} (hD : H.D = D) {G : Hash} (hG : HashOK G) {g : Fns} {pg : Addr}
    (Tg : TabS G g gArg Sp s pg) {Gm : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGl : Gm.len = G.D) (hGv : Proof.Mgf1.Valid Gm) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → t'.syms = s.syms →
      (∀ o < oSt, view t'.mem (Sp s) o = dbV Gm (view t.mem (Sp s)) lN dN D c o) → WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) rest))) t Q := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hd1 := L.d1; have hD64 := L.D64
  refine WP.seq (WP.mono_syms (dbArgs_ok L hD h) fun t₄ ⟨b₄, k₄, x24, x25, x26, x27⟩ y₄ => ?_)
  refine WP.seq (WP.mono (mgfXorT_ok F hG Tg hGh hGl hGv (src := lN + dN) (srcLen := D) (dst := lN) (dstLen := dN)
    ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩ b₄ (y₄.trans sy) x24 x25 x26 x27)
    fun t₅ ⟨⟨b₅, v₅⟩, y₅⟩ => ?_)
  obtain V4 : view t₄.mem (Sp s) = view t.mem (Sp s) := by rw [k₄.mem]
  rw [V4] at v₅
  refine WP.seq (WP.mono_syms (clearTop_ok L b₅) fun w ⟨b, _, v⟩ yw => k w b (yw.trans y₅) fun o ho => ?_)
  rw [v o ho, dbV]
  by_cases e : o = lN
  · subst e; rw [ifp rfl, ifp rfl, v₅ _ ho]
  · rw [ifn e, ifn e, v₅ o ho]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Scan`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: the first nonzero byte of `DB`

Untrusted: everything here is checked by Lean. `scan_ok`: `scan` finds, in
the `dbLen` bytes of `DB` (`w`), the number `z` of leading zero bytes
(`Proof.RsaPss.lz`) without branching on them: `pos` (`r8`) is `z` and `val`
(`r9`) the byte there if `z < dbLen`, both 0 if not. The invariant after `i`
bytes is that of their leading zeros (`lzr w i`, `lzr_succ`), with `r7` all
ones while it is `i`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_and wp_or wp_lsr
  wp_lbz wp_nil wp_countdown)
open VG.Proof.RsaPss (lz)
open VG.Proof.Mgf1 (ifp ifn)

/-- The leading zeros of the first `i` bytes of `w`. -/
def lzr (w : Nat → Byte) (i : Nat) : Nat := lz ((List.range i).map w)

theorem lz_append : ∀ (l : List Byte) (x : Byte),
    lz (l ++ [x]) = if lz l = l.length then (if x = 0 then l.length + 1 else l.length) else lz l
  | [], x => by simp only [List.nil_append, lz, List.length_nil]; split <;> simp
  | b :: bs, x => by
    rw [List.cons_append, lz, lz, lz_append bs x, List.length_cons]
    have := VG.Proof.RsaPss.lz_le bs
    by_cases hb : b = 0 <;> by_cases h : lz bs = bs.length <;> by_cases hx : x = 0 <;>
      simp only [hb, h, hx, ite_true, ite_false, Nat.add_right_cancel_iff] <;> (try split) <;> omega_arith

theorem lzr_succ (w : Nat → Byte) (i : Nat) :
    lzr w (i + 1) = if lzr w i = i then (if w i = 0 then i + 1 else i) else lzr w i := by
  have := lz_append ((List.range i).map w) (w i)
  rw [List.length_map, List.length_range] at this
  rw [lzr, List.range_succ, List.map_append, List.map_singleton, this, lzr]

theorem lzr_le (w : Nat → Byte) (i : Nat) : lzr w i ≤ i := by
  have := VG.Proof.RsaPss.lz_le ((List.range i).map w); simpa [lzr] using this

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem isz_eq (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  obtain e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- What the scan keeps after `i` bytes: `r7` all ones while every byte so
far is zero, `pos` and `val` once one is not. -/
structure ScanI (w : Nat → Byte) (S : Addr) (lN i : Nat) (u : State) : Prop where
  r4 : u.gpr .r4 = off S (lN + i)
  r6 : u.gpr .r6 = BitVec.ofNat 64 i
  r7 : u.gpr .r7 = if lzr w i = i then BitVec.allOnes 64 else 0#64
  r8 : u.gpr .r8 = BitVec.ofNat 64 (if lzr w i < i then lzr w i else 0)
  r9 : u.gpr .r9 = (if lzr w i < i then w (lzr w i) else 0).setWidth 64

theorem scan_step {w : Nat → Byte} {S : Addr} {lN i : Nat} {u u' : State} (I : ScanI w S lN i u)
    (hb : (u'.gpr .r10) = (w i).setWidth 64)
    (h11 : u'.gpr .r11 = (u'.gpr .r10 - BitVec.ofNat 64 1) >>> 63)
    (h12 : u'.gpr .r12 = (u'.gpr .r11 - BitVec.ofNat 64 1) &&& u.gpr .r7)
    (h8 : u'.gpr .r8 = u.gpr .r8 ||| (u.gpr .r6 &&& u'.gpr .r12))
    (h9 : u'.gpr .r9 = u.gpr .r9 ||| (u'.gpr .r10 &&& u'.gpr .r12))
    (h7 : u'.gpr .r7 = u.gpr .r7 &&& (BitVec.ofNat 64 0 - u'.gpr .r11))
    (h4 : u'.gpr .r4 = u.gpr .r4 + BitVec.ofNat 64 1) (h6 : u'.gpr .r6 = u.gpr .r6 + BitVec.ofNat 64 1) :
    ScanI w S lN (i + 1) u' := by
  obtain hz := isz_eq (w i)
  rw [← hb] at hz
  rw [hz] at h11
  obtain hl := lzr_le w i
  obtain r4' : u'.gpr .r4 = off S (lN + (i + 1)) := by rw [h4, I.r4]; exact off_off _ _ _
  obtain r6' : u'.gpr .r6 = BitVec.ofNat 64 (i + 1) := by rw [h6, I.r6, BitVec.ofNat_add]
  by_cases e : lzr w i = i
  · have I7 := I.r7; have I8 := I.r8; have I9 := I.r9
    rw [ifp e] at I7
    rw [ifn (by omega_using [e])] at I8 I9
    by_cases z : w i = 0
    · rw [ifp z] at h11
      obtain h12' : u'.gpr .r12 = 0#64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifp z]
      · rw [ifp rfl, h7, I7, h11]; rfl
      · rw [ifn (by omega_using []), h8, I8, h12', BitVec.and_zero, BitVec.or_zero]
      · rw [ifn (by omega_using []), h9, I9, h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifn z] at h11
      obtain h12' : u'.gpr .r12 = BitVec.allOnes 64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifn z]
      · rw [ifn (by omega_using []), h7, I7, h11]; rfl
      · rw [ifp (by omega_using []), h8, I8, h12', BitVec.and_allOnes, I.r6]; simp
      · rw [ifp (by omega_using []), h9, I9, h12', BitVec.and_allOnes, hb, ← e]; simp
  · have I7 := I.r7
    rw [ifn e] at I7
    obtain h12' : u'.gpr .r12 = 0#64 := by rw [h12, I7, BitVec.and_zero]
    refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifn e]
    · rw [ifn (by omega_using [hl]), h7, I7, BitVec.zero_and]
    · rw [ifp (by omega_using [hl]), h8, I.r8, ifp (by omega_using [hl, e]), h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifp (by omega_using [hl]), h9, I.r9, ifp (by omega_using [hl, e]), h12', BitVec.and_zero, BitVec.or_zero]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- The scan of `DB`'s `dbLen` bytes, `w`, at `S + lo`. -/
theorem scan_ok {t : State} (h : Base Sp (vP D) s t) {w : Nat → Byte}
    (hw : ∀ j < dN, view t.mem (Sp s) (lN + j) = w j) :
    WP isa scan t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r24, .r25, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) ∧
      t'.gpr .r8 = BitVec.ofNat 64 (if lzr w dN < dN then lzr w dN else 0) ∧
      t'.gpr .r9 = (if lzr w dN < dN then w (lzr w dN) else 0).setWidth 64 := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hl := L.l1; have hd1 := L.d1
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_li (by decide) fun t₄ o₄ e₄ => wp_subi fun t₅ o₅ e₅ => wp_li (by decide) fun t₆ o₆ e₆ =>
    wp_li (by decide) fun t₇ o₇ e₇ => wp_nil ?_)
  obtain k₇ : Only [.r4, .r5, .r6, .r7, .r8, .r9] t t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  obtain I0 : ScanI w (Sp s) lN 0 t₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, h.plo, L.hlo]; rfl
    · rw [o₇.get .r6, o₆.get .r6, o₅.get .r6, o₄.get .r6, e₃]
    · rw [o₇.get .r7, o₆.get .r7, e₅, e₄]; rfl
    · rw [o₇.get .r8, e₆]; rfl
    · rw [e₇]; rfl
  refine WP.mono (wp_countdown (cnt := .r5) (N := dN) (by omega_using [hk]) (by omega_using [hd1])
    (fun i u => ScanI w (Sp s) lN i u ∧ Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t₇ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, o₁.get .r21, h.pdb, L.hdb]))
    fun u ⟨I, o⟩ => ?_
  · intro i hi u ⟨I, o⟩ hc
    refine wp_lbz (a := off (Sp s) (lN + i)) (by rw [I.r4, BitVec.add_zero])
      (by rw [o.rd, o.wr, k₇.rd, k₇.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_using [hk, hk2, hi]) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_and fun u₅ p₅ f₅ =>
      wp_and fun u₆ p₆ f₆ => wp_or fun u₇ p₇ f₇ => wp_and fun u₈ p₈ f₈ => wp_or fun u₉ p₉ f₉ =>
      wp_li (by decide) fun u₁₀ p₁₀ f₁₀ => wp_sub fun u₁₁ p₁₁ f₁₁ => wp_and fun u₁₂ p₁₂ f₁₂ =>
      wp_addi fun u₁₃ p₁₃ f₁₃ => wp_addi fun u₁₄ p₁₄ f₁₄ => wp_subi fun u₁₅ p₁₅ f₁₅ => wp_nil ?_
    obtain q : Only [.r10, .r11, .r12, .r3, .r8, .r9, .r7, .r4, .r6, .r5] u u₁₅ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))))))))))).mono
    obtain v₁ : u₁₅.gpr .r10 = (w i).setWidth 64 := by
      rw [p₁₅.get .r10, p₁₄.get .r10, p₁₃.get .r10, p₁₂.get .r10, p₁₁.get .r10, p₁₀.get .r10,
        p₉.get .r10, p₈.get .r10, p₇.get .r10, p₆.get .r10, p₅.get .r10, p₄.get .r10, p₃.get .r10, p₂.get .r10, f₁,
        o.mem, k₇.mem, ← hw i hi]; rfl
    obtain p₁' : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9], u₁.gpr r = u.gpr r := fun r hr => p₁.get r (by revert r; decide)
    refine ⟨⟨scan_step I v₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩ <;>
      simp (disch := decide) only [p₁₅.gpr, p₁₄.gpr, p₁₃.gpr, p₁₂.gpr, p₁₁.gpr, p₁₀.gpr, p₉.gpr, p₈.gpr, p₇.gpr, p₆.gpr, p₅.gpr, p₄.gpr, p₃.gpr, p₂.gpr, f₁₅, f₁₄, f₁₃, f₁₂, f₁₁, f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, f₂, p₁' _ (by decide : Reg.r4 ∈ _), p₁' _ (by decide : Reg.r5 ∈ _), p₁' _ (by decide : Reg.r6 ∈ _),
        p₁' _ (by decide : Reg.r7 ∈ _), p₁' _ (by decide : Reg.r8 ∈ _), p₁' _ (by decide : Reg.r9 ∈ _)]
  · have kk : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t u := (k₇.trans o).mono
    refine ⟨h.only F kk, by rw [o.mem, k₇.mem], fun r hr => ?_, I.r8, I.r9⟩
    exact kk.gpr r (by revert r; decide)

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Check`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: the delimiter and the salt's length

Untrusted: everything here is checked by Lean. `check_ok`: `posCheck` and
`lenCheck` put in `r24` the accumulator, `EM`'s last byte (the first checks)
ORed with `val ⊕ 1` and, for a given salt length, with its difference from
the salt's (`accW`), and in `r25` the salt's length `dbLen - pos - 1`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_or wp_lbz wp_nil
  eval_zero)
open VG.Proof.Mgf1 (ifp ifn)

/-- The accumulator after the delimiter's and the salt length's checks. -/
def accW (a : Byte) (val : BitVec 64) (sl : Nat) (any saltLen : BitVec 64) : BitVec 64 :=
  (a.setWidth 64 ||| (val ^^^ 1#64)) ||| if any = 0 then BitVec.ofNat 64 sl ^^^ saltLen else 0#64

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `posCheck`: the accumulator with `val ⊕ 1`, and the salt's length. -/
theorem posCheck_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) :
    WP isa (.block posCheck) t fun t' => Base Sp (vP D) s t' ∧ Only [.r4, .r24, .r3, .r9, .r25] t t' ∧
      t'.gpr .r24 = a.setWidth 64 ||| (val ^^^ 1#64) ∧ t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2
  generalize hK : (s.gpr .r4).toNat = kN at hk hk2 ha
  refine wp_add fun t₁ o₁ e₁ => wp_subi fun t₂ o₂ e₂ => ?_
  obtain a₂ : t₂.gpr .r4 = off (Sp s) (kN - 1) := by
    rw [e₂, e₁, h.r14, h.pk, ← ofNat_toNat (s.gpr .r4), hK, off_sub _ (by omega_using [hk]) (by omega_using [hK])]
  refine wp_lbz (a := off (Sp s) (kN - 1)) (by rw [a₂, BitVec.add_zero])
    (by rw [o₂.rd, o₁.rd, o₂.wr, o₁.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_using [hk2]) _) fun t₃ o₃ e₃ => ?_
  refine wp_li (by decide) fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ => wp_or fun t₆ o₆ e₆ =>
    wp_sub fun t₇ o₇ e₇ => wp_subi fun t₈ o₈ e₈ => wp_nil ?_
  obtain k₈ : Only [.r4, .r24, .r3, .r9, .r25] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  refine ⟨h.only F k₈, k₈, ?_, ?_⟩
  · rw [o₈.get .r24, o₇.get .r24, e₆, o₅.get .r24, o₄.get .r24, e₃, e₅, o₄.get .r9, o₃.get .r9, o₂.get .r9,
      o₁.get .r9, h9, e₄, o₂.mem, o₁.mem, ← ha]; rfl
  · rw [e₈, e₇, o₆.get .r21, o₅.get .r21, o₄.get .r21, o₃.get .r21, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb,
      o₆.get .r8, o₅.get .r8, o₄.get .r8, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8,
      Offset.ofNat_sub_ofNat (show pos ≤ dN by omega_using [hp]), Offset.ofNat_sub_ofNat (show 1 ≤ dN - pos by omega_using [hp])]

/-- `lenCheck`: for a given salt length, the accumulator with the salt's
length's difference from it. -/
theorem lenCheck_ok {t : State} (h : Base Sp (vP D) s t) {v : BitVec 64} {sl : Nat} (h24 : t.gpr .r24 = v)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa lenCheck t fun t' => Base Sp (vP D) s t' ∧ Only [.r3, .r24] t t' ∧
      t'.gpr .r24 = v ||| if anyL s = 0 then BitVec.ofNat 64 sl ^^^ stackArg s 0 else 0#64 := by
  have F := L.F
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have ha0 : anyL s = 0 := by rw [← h.pany]; simpa using hz
    refine wp_xor fun w₁ p₁ f₁ => wp_or fun w p f => ?_
    obtain q : Only [.r3, .r24] t w := (p₁.trans p).mono
    refine wp_nil ⟨h.only F q, q, ?_⟩
    rw [f, p₁.get .r24, h24, f₁, h25, h.psl, ifp ha0]
  · have ha0 : anyL s ≠ 0 := by rw [← h.pany]; simpa using hz
    refine wp_nil ⟨h, Only.refl _ t, ?_⟩
    rw [h24, ifn ha0, BitVec.or_zero]

theorem check_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → t'.mem = t.mem →
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r8, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) →
      t'.gpr .r24 = accW a val (dN - pos - 1) (anyL s) (stackArg s 0) →
      t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) → t'.syms = t.syms → WP isa rest t' Q) :
    WP isa (.seq (.block posCheck) (.seq lenCheck rest)) t Q :=
  WP.seq (WP.mono_syms (posCheck_ok L h ha h8 hp h9) fun t₈ ⟨b₈, k₈, x24, x25⟩ y₈ =>
    WP.seq (WP.mono_syms (lenCheck_ok L b₈ x24 x25) fun w ⟨b, q, x⟩ yw => k w b (by rw [q.mem, k₈.mem])
      (fun r hr => by rw [q.gpr r (by revert r; decide), k₈.gpr r (by revert r; decide)])
      (by rw [x]; rfl) (by rw [q.get .r25, x25]) (yw.trans y₈)))

end

end VG.Proof.RsaPss.PPC64LE

end

end


/-!
# RSASSA-PSS verification on PPC64LE: after the public operation

Untrusted: everything here is checked by Lean. `post_ok`: from `EM` in its
place (the view `V`), the code after the call returns 1 exactly when `Res`
holds: the accumulator of the checks (`accR`: `0xbc`, the leading byte, the
top bits, the delimiter and, for a given salt length, the salt's length) is
zero and `H` is the hash of `M'` (`mR`), from `DB` unmasked (`dbV`), the first
nonzero byte of `DB` (`lzr`) and the salt's length.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa Fns mgfXorT)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil eval_zero)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaOaep (mixV srcB)

section
variable (Gm Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (D lN dN : Nat) (c : Byte) (k : Nat) (mh : List Byte)
  (any saltLen : BitVec 64)

/-- `EM` after `acc0`. -/
def v1 : Nat → Byte := fun o => if o = k - 1 then accB V lN c k else V o

/-- `DB`'s bytes, unmasked. -/
def wR (j : Nat) : Byte := dbV Gm (v1 V lN c k) lN dN D c (lN + j)

/-- The position of the first nonzero byte of `DB`, and its value. -/
def posR : Nat := if lzr (wR Gm V D lN dN c k) dN < dN then lzr (wR Gm V D lN dN c k) dN else 0
def valR : Byte := if lzr (wR Gm V D lN dN c k) dN < dN then wR Gm V D lN dN c k (lzr (wR Gm V D lN dN c k) dN) else 0

/-- The salt's length. -/
def slR : Nat := dN - posR Gm V D lN dN c k - 1

/-- The accumulator. -/
def accR : BitVec 64 :=
  accW (accB V lN c k) ((valR Gm V D lN dN c k).setWidth 64) (slR Gm V D lN dN c k) any saltLen

/-- `M'`. -/
def mR : List Byte :=
  if any = 0 then mFix (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN saltLen.toNat
  else mAny (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k)

/-- What makes the result 1. -/
def Res : Prop :=
  accR Gm V D lN dN c k any saltLen = 0#64 ∧
    ∀ i < D, V (lN + dN + i) = (Gs.hash (mR Gm V D lN dN c k mh any saltLen)).getD i 0

instance : Decidable (Res Gm Gs V D lN dN c k mh any saltLen) := by unfold Res; infer_instance

end

theorem dbV_congr {Gm : Spec.Mgf1.Hash} {V V' : Nat → Byte} {lN dN D : Nat} {c : Byte} (hf : lN + dN + D ≤ 1024)
    (h : ∀ o < 1024, V o = V' o) {o : Nat} (ho : o < 1024) : dbV Gm V lN dN D c o = dbV Gm V' lN dN D c o := by
  obtain hs : srcB V (lN + dN) D = srcB V' (lN + dN) D :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; omega_arith)
  simp only [dbV, mixV, hs, h o ho]

theorem xor1_lt (b : Byte) : ((b.setWidth 64) ^^^ 1#64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (byte_lt b) (by decide)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
include L hH

theorem post_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    {G : Hash} (hG : HashOK G) {g : Fns} {pg : Addr} (Tg : TabS G g gArg Sp s pg) {Gm : Spec.Mgf1.Hash}
    (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
    {cn dn : String} {cc dc : Prog isa} {f : MdFns} {p : Addr} (T : MdTabS H cn cc dn dc f hArg Sp s p)
    {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
    (hN : H.N = P.N) (hB : H.B = P.B) {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ dN) :
    WP isa (.seq (.block acc0) (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) (.seq scan
      (.seq (.block posCheck) (.seq lenCheck (finish H P f)))))))) t fun t' => Base Sp (vP D) s t' ∧
      t'.gpr .r3 = if Res Gm Gs (view t.mem (Sp s)) D lN dN c (s.gpr .r4).toNat (mh D s) (anyL s) (stackArg s 0)
        then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  generalize hK : (s.gpr .r4).toNat = k at hk hk2
  let V := view t.mem (Sp s)
  refine WP.seq (WP.mono_syms (acc0_ok L h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  rw [hK] at v₁
  refine unmask_ok L hD hG Tg hGmh hGml hGmv b₁ (y₁.trans sy) fun t₂ b₂ y₂ v₂ => ?_
  obtain e₁ : ∀ o < 1024, view t₁.mem (Sp s) o = v1 V lN c k o := fun o ho => by rw [v₁ o (by omega_arith)]; rfl
  obtain W : ∀ o < 1024, view t₂.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [v₂ o (by omega_arith), dbV_congr (by omega_arith) e₁ ho]
  refine WP.seq (WP.mono_syms (scan_ok L b₂ (w := wR Gm V D lN dN c k) fun j hj => by rw [W _ (by omega_arith)]; rfl)
    fun t₃ ⟨b₃, m₃, g₃, x8, x9⟩ y₃ => ?_)
  obtain hpos : posR Gm V D lN dN c k < dN := by
    unfold posR; split <;> omega_arith
  obtain ha : view t₃.mem (Sp s) ((s.gpr .r4).toNat - 1) = accB V lN c k := by
    rw [hK, m₃, W _ (by omega_arith), dbV]
    simp only [mixV]
    rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifp rfl]
  refine check_ok L b₃ (a := accB V lN c k) (pos := posR Gm V D lN dN c k)
    (val := (valR Gm V D lN dN c k).setWidth 64) ha x8 hpos x9 fun t₄ b₄ m₄ g₄ x24 x25 y₄ => ?_
  obtain sy₄ : t₄.syms = s.syms := y₄.trans (y₃.trans y₂)
  obtain W₄ : ∀ o < 1024, view t₄.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [m₄, m₃, W o ho]
  obtain vH : ∀ i < D, dbV Gm (v1 V lN c k) lN dN D c (lN + dN + i) = V (lN + dN + i) := fun i hi => by
    simp only [dbV, mixV]; rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifn (by omega_arith)]
  obtain hacc : (t₄.gpr .r24).toNat < 2 ^ 63 := by
    rw [x24, accW]
    refine or_lt (or_lt (byte_lt _) (xor1_lt _)) ?_
    split
    · rename_i h0
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
      have := hfit h0
      exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
    · decide
  have x24' : t₄.gpr .r24 = accR Gm V D lN dN c k (anyL s) (stackArg s 0) := x24
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  all_goals have g20 : t₄.gpr .r20 = anyL s := by rw [g₄ _ (by decide), g₃ _ (by decide), b₂.pany]
  · have h0 : anyL s = 0 := by rw [g20] at hz; simpa using hz
    obtain hM : mFix (view t₄.mem (Sp s)) (mh D s) lN dN (stackArg s 0).toNat =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifp h0]
      have := hfit h0
      simp only [mFix]
      refine congrArg (_ ++ ·) (List.map_congr_left fun j hj => W₄ _ ?_)
      have := List.mem_range.mp hj; omega_arith
    refine WP.mono (fixed_ok L hH T hD hGh b₄ sy₄ (hfit h0) hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]
  · have h0 : anyL s ≠ 0 := by rw [g20] at hz; simpa using hz
    obtain hM : mAny (view t₄.mem (Sp s)) (mh D s) lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k) =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifn h0]
      simp only [mAny]
      refine congrArg (List.replicate 8 0 ++ mh D s ++ ·) (List.map_congr_left fun j hj => ?_)
      split
      · rw [W₄ _ (by omega_arith)]
      · rfl
    obtain hsl : slR Gm V D lN dN c k + posR Gm V D lN dN c k + 1 = dN := by unfold slR; omega_arith
    refine WP.mono (any_ok L hH T hD hGh ok hl hN hB b₄ sy₄ (pos := posR Gm V D lN dN c k)
      (sl := slR Gm V D lN dN c k) (by rw [g₄ _ (by decide), x8]; rfl) hpos x25 hsl hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE
