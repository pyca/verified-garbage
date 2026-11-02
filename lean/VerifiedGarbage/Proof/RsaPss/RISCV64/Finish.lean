module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Any
import VerifiedGarbage.Proof.RsaPss.RISCV64.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPss.RISCV64.Shift
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix

/-!
# RSASSA-PSS verification on RISC-V: `H'` and the result

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Finish.lean`): `fixed_ok` and `any_ok`: the
two branches of `finish`, from the state after the checks of `DB`: the
result is 1 exactly when the accumulator is zero and `H` is the hash of
`M' = 0⁸ ‖ mHash ‖ salt` (`mFix`: the last `salt_len` bytes of `DB`;
`mAny`: the `sl` bytes after `pos`), as views of `EM`'s place.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view fx Same hfits offs)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_sll wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `M'` for a given salt length `sl`: the last `sl` bytes of `DB` (at `lo`,
`dbLen` bytes, in the view `V`). -/
def mFix (V : Nat → Byte) (mh : List Byte) (lN dN sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => V (lN + dN - sl + j)

/-- `M'` for any salt length: the `sl` bytes of `DB` after `pos`. -/
def mAny (V : Nat → Byte) (mh : List Byte) (lN dN pos sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => if j + (pos + 1) < dN then V (lN + (j + (pos + 1))) else 0

/-- The bytes of `M'` at `oY`, from their view. -/
theorem mB_eq {m : Mem} {S : Addr} {D n : Nat} {mh rest : List Byte} (hmh : mh.length = D)
    (hr : rest.length = n) (h : ∀ i < 8 + D + n, view m S (oY + i) = (List.replicate 8 0 ++ mh ++ rest).getD i 0) :
    mB m S (8 + D + n) = List.replicate 8 0 ++ mh ++ rest := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hmh, hr]; omega)
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
  · rw [ifp h₁, List.getElem?_append_left (by simp; omega), List.getElem?_replicate, ifp h₁]; rfl
  · rw [ifn h₁, List.getElem?_append_right (by simp; omega), List.length_replicate]
    by_cases h₂ : i < 8 + D
    · rw [ifp h₂, List.getElem?_append_left (by omega)]
    · rw [ifn h₂, List.getElem?_append_right (by omega), hmh, Nat.sub_sub]

/-- `t5 := 8`. -/
theorem nset8 {u : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Only [.t5] u u' → u'.gpr .t5 = BitVec.ofNat 64 8 → WP isa (.block is) u' Q) :
    WP isa (.block ([.li .t5 8] ++ is)) u Q :=
  wp_li (imm := 8) (by decide) k

/-- `t5 := 2048`. -/
theorem nset2048 {u : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Only [.t5] u u' → u'.gpr .t5 = BitVec.ofNat 64 2048 → WP isa (.block is) u' Q) :
    WP isa (.block ([.li .t5 1024, .shift .sll .d .t5 .t5 1] ++ is)) u Q :=
  wp_li (imm := 1024) (by decide) fun u₁ o₁ e₁ => wp_sll fun u₂ o₂ e₂ =>
    k u₂ (o₁.trans o₂).mono (by rw [e₂, e₁]; rfl)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
  (hF : H.F ≤ 208)
include L hH hF

theorem fixed_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State}
    (h : Base Sp (vP D) s t) (x : Xs s t) (hsl : (s.gpr .a7).toNat + 1 ≤ dN) (ha : (t.gpr .s10).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H [.li .t5 8]) (.seq (copySalt H) (.seq (hashFixed H) (cmpH H oDig)))) t fun t' =>
      Base Sp (vP D) s t' ∧ t'.gpr .a0 = if t.gpr .s10 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN (s.gpr .a7).toNat)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2048 := rfl
  refine WP.seq (WP.mono (prefix_ok L hD (n := 8) (Nat.le_refl _) (by decide) nset8 h) fun t₁ ⟨b₁, g₁, v₁⟩ => ?_)
  have x₁ : Xs s t₁ := x.of fun r hr => g₁.gpr r (by revert r; decide)
  refine WP.seq (WP.mono (salt_ok L hD b₁ x₁ hsl) fun t₂ ⟨b₂, g₂, v₂⟩ => ?_)
  generalize hS : (s.gpr .a7).toNat = sl at hsl v₂
  have h6 : t₂.gpr .s6 = BitVec.ofNat 64 sl := by
    rw [g₂.get .s6, x₁.s6, ← hS, ofNat_toNat]
  refine WP.seq (WP.mono (hashFixedG_ok F hH hF hD h6 b₂ (by omega)) fun t₃ ⟨b₃, g₃, s₃, d₃⟩ => ?_)
  have g24 : t₃.gpr .s10 = t.gpr .s10 := by
    rw [g₃ _ (by decide), g₂.get .s10, g₁.get .s10]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega) (by decide) b₃ (by rw [g24]; exact ha))
    fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  have vH : ∀ i < D, view t₃.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [s₃ _ (by omega) (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> simp only <;> omega),
      v₂ _ (by omega), ifn (by omega), v₁ _ (by omega), ifn (by omega), ifn (by omega)]
  have hM : mB t₂.mem (Sp s) (8 + D + sl) = mFix (view t.mem (Sp s)) (mh D s) lN dN sl := by
    refine mB_eq (by simp [Spec.Rsa.bytesAt]) (by simp) fun i hi => ?_
    rw [getD_m3 (D := D) (by simp [Spec.Rsa.bytesAt]), v₂ _ (by omega)]
    by_cases h₁ : i < 8
    · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega), v₁ _ (by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 8 by omega), ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega), v₁ _ (by omega),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega), ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega]
      · rw [ifp (show oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl by omega), v₁ _ (by omega),
          ifn (show ¬(oY + 8 ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8 + D) by omega),
          ifn (show ¬(oY ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8) by omega), ifn h₁, ifn h₂]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i - 8 - D < sl by omega),
          Option.map_some, Option.getD_some]
        congr 2; omega
  have vD : ∀ i < D, view t₃.mem (Sp s) (oDig + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0 := fun i hi => by
    have d₃' := d₃
    rw [show Spec.Sha256.bytesAt t₂.mem (off (Sp s) oY) (8 + D + sl) = _ from hM] at d₃'
    have := congrArg (·.getD i 0) d₃'
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < H.D by omega), Option.map_some, Option.getD_some] at this
    rw [view, ← off_off, this, hGh, List.getD_eq_getElem?_getD]
  by_cases e : t.gpr .s10 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

theorem any_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State}
    (h : Base Sp (vP D) s t) {pos sl : Nat} (h8 : t.gpr .s8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h25 : t.gpr .s11 = BitVec.ofNat 64 sl) (hsl : sl < dN) (ha : (t.gpr .s10).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H [.li .t5 1024, .shift .sll .d .t5 .t5 1]) (.seq (copyDb H) (.seq (shift H)
      (.seq (hashAny H) (cmpH H oSel))))) t fun t' =>
      Base Sp (vP D) s t' ∧ t'.gpr .a0 = if t.gpr .s10 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2048 := rfl
  have hB : oBk = 1376 := rfl
  have hS : oSel = 1568 := rfl
  refine WP.seq (WP.mono (prefix_ok L hD (n := 2048) (by decide) (Nat.le_refl _) nset2048 h)
    fun t₁ ⟨b₁, g₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (copyDb_ok L hD b₁) fun t₂ ⟨b₂, g₂, v₂⟩ => ?_)
  refine WP.seq (WP.mono (shift_ok L hD b₂ (pos := pos) (by rw [g₂.get .s8, g₁.get .s8, h8]) hp)
    fun t₃ ⟨b₃, k₃, v₃⟩ => ?_)
  refine WP.seq (WP.mono (hashAny_ok L hH hF hD b₃ hsl (by rw [k₃.get .s11, g₂.get .s11, g₁.get .s11, h25]))
    fun t₄ ⟨b₄, g₄, s₄, d₄⟩ => ?_)
  have g24 : t₄.gpr .s10 = t.gpr .s10 := by
    rw [g₄ _ (by decide), k₃.get .s10, g₂.get .s10, g₁.get .s10]
  refine WP.mono (cmpH_ok L hD (o := oSel) (by omega) (by decide) b₄ (by rw [g24]; exact ha))
    fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  let b := oY + 8 + D
  have w₂ : ∀ o < oRsa, ¬(b ≤ o ∧ o < b + dN) → ¬(oY ≤ o ∧ o < oY + 2048) → view t₂.mem (Sp s) o = view t.mem (Sp s) o :=
    fun o ho h₁ h₂ => by rw [v₂ o ho, ifn h₁, v₁ o ho, ifn (by omega), ifn h₂]
  have vH : ∀ i < D, view t₄.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [s₄ _ (by omega) (fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega),
      v₃ _ (by omega), shV_out _ _ _ _ _ _ (by omega), w₂ _ (by omega) (by omega) (by omega)]
  have hz : ∀ x, dN ≤ x → x < dN + 2 ^ 9 → view t₂.mem (Sp s) (b + x) = 0 := fun x h₁ h₂ => by
    have : (2 : Nat) ^ 9 = 512 := rfl
    rw [v₂ _ (by omega), ifn (by omega), v₁ _ (by omega), ifn (by omega), ifp (by omega)]
  have hM : mB t₃.mem (Sp s) (8 + D + sl) = mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl := by
    refine mB_eq (by simp [Spec.Rsa.bytesAt]) (by simp) fun i hi => ?_
    rw [getD_m3 (D := D) (by simp [Spec.Rsa.bytesAt]), v₃ _ (by omega)]
    by_cases h₁ : i < 8
    · rw [shV_out _ _ _ _ _ _ (by omega), v₂ _ (by omega), ifn (by omega), v₁ _ (by omega),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega), ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [shV_out _ _ _ _ _ _ (by omega), v₂ _ (by omega), ifn (by omega), v₁ _ (by omega),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega), ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega]
      · rw [show oY + i = b + (i - 8 - D) by omega, shV_eq _ (by omega) hz (by omega), ifn h₁, ifn h₂]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i - 8 - D < sl by omega),
          Option.map_some, Option.getD_some]
        by_cases e : i - 8 - D + (pos + 1) < dN
        · rw [ifp e, ifp e, v₂ _ (by omega), ifp (by omega), v₁ _ (by omega), ifn (by omega), ifn (by omega)]
          congr 1; omega
        · rw [ifn e, ifn e]
  have vD : ∀ i < D, view t₄.mem (Sp s) (oSel + i) =
      (Gs.hash (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl)).getD i 0 := fun i hi => by
    rw [d₄ i hi, ← hM, hGh]
  by_cases e : t.gpr .s10 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
      (Gs.hash (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl)).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.RISCV64
