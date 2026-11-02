module

-- separate module: it builds in parallel with `Unmask`, `Scan` and `Check`, which `Post` also needs.

import VerifiedGarbage.Proof.RsaPss.RISCV64.Select
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Hash
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
import VerifiedGarbage.Proof.RsaPss.RISCV64.Cmp
import VerifiedGarbage.Proof.RsaPss.RISCV64.Shift

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

/-!
# RSASSA-PSS verification on RISC-V: `H'` for any salt length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Any.lean`): `hashAny_ok`, after `0⁸ ‖ mHash`, for
each length `L < dbLen` (`lenRound_ok`) the streaming state is copied to
`oBk`, finalized, its digest kept at `oSel` if `L` is the salt's length
`sl`, copied back and updated with the next byte of `M'`: the state
represents the first `8 + hLen + L` bytes of `M'` (`AnyI`), and after the
loop `oSel` holds the hash of the first `8 + hLen + sl`.
-/


namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view fx Same hfits offs)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_nil)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- The first `n` bytes of `M'`. -/
abbrev mB (m : Mem) (S : Addr) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (off S oY) n

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    Spec.Sha256.bytesAt m p (n + 1) =
      Spec.Sha256.bytesAt m p n ++ Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 n) 1 := by
  simp [Spec.Sha256.bytesAt, List.range_succ]

theorem same_of_if {S : Addr} {t t' : State} {b n : Nat} {f : Nat → Byte}
    (h : ∀ o < oRsa, view t'.mem S o = if b ≤ o ∧ o < b + n then f o else view t.mem S o) :
    Same S t t' [(b, n)] :=
  fun o ho hr => by
    have := hr (b, n) (List.mem_singleton_self _)
    rw [h o ho, ifn (by simp only at this; omega)]

/-- The registers the loop keeps. -/
abbrev kpA : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s10, .s11]

/-- The ranges the loop writes. -/
abbrev wrA (H : Hash) : List (Nat × Nat) := [(oSt, H.S), (oDig, H.D), (oBk, H.S), (oSel, H.D)]

/-- After `L` lengths, from the state `t₀` before the loop. -/
structure AnyI {H : Hash} (hH : HashOK H) (D : Nat) (s t₀ : State) (sl L : Nat) (u : State) : Prop where
  base : Base Sp (vP D) s u
  g : ∀ r ∈ kpA, u.gpr r = t₀.gpr r
  s8 : u.gpr .s8 = BitVec.ofNat 64 L
  repr : hH.SH.Repr u.mem (off (Sp s) oSt) (mB t₀.mem (Sp s) (8 + D + L))
  same : Same (Sp s) t₀ u (wrA H)
  sel : sl < L → ∀ i < D, view u.mem (Sp s) (oSel + i) =
    (hH.SH.H.hash (mB t₀.mem (Sp s) (8 + D + sl))).getD i 0

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
  (hF : H.F ≤ 208)
include L hH hF

theorem lenRound_ok (hD : H.D = D) {t₀ : State} {sl Ln : Nat} (hsl : sl < dN)
    (h25 : t₀.gpr .s11 = BitVec.ofNat 64 sl) (hL : Ln < dN) {u : State} (I : AnyI hH D s t₀ sl Ln u) :
    WP isa (lenRound H) u fun u' => AnyI hH D s t₀ sl (Ln + 1) u' ∧
      u'.gpr .s9 = u.gpr .s9 - BitVec.ofNat 64 1 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2048 := rfl
  have hB : oBk = 1376 := rfl
  have hS : oSel = 1568 := rfl
  have hN := hH.hN
  have hHS : H.S < 2048 := by omega
  have hS0 : 0 < H.S := by simp only [Hash.S]; omega
  let m := mB t₀.mem (Sp s) (8 + D + Ln)
  have hml : m.length = 8 + D + Ln := by simp [m, Spec.Sha256.bytesAt]
  -- The state to `oBk`.
  refine WP.seq (WP.mono (copyN_ok L I.base (a := oSt) (b := oBk) (n := H.S) hS0
    hHS (by omega) (by omega) (.inl (by omega)) (by omega) (by decide)) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  have s₁ : Same (Sp s) u u₁ [(oBk, H.S)] := same_of_if v₁
  have r₁ : hH.SH.Repr u₁.mem (off (Sp s) oSt) m :=
    hH.congr u.mem u₁.mem _ _ (fun i hi => by
      have := s₁ (oSt + i) (by omega) (fun p hp => by simp at hp; subst hp; omega)
      simp only [view] at this; rw [← off_off] at this; exact this) I.repr
  -- `finalize`.
  refine WP.seq (wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun u₂ o₂ e₂ => wp_nil ?_)
  have b₂ := b₁.only F o₂
  have g26 : u₁.gpr .s8 = BitVec.ofNat 64 Ln := by rw [k₁.get .s8, I.s8]
  refine WP.seq (WP.mono (hFin_ok F hH hF b₂ (m := m) (by rw [o₂.mem]; exact r₁)
    (by rw [e₂, g26, ← BitVec.ofNat_add, hml, hD]; congr 1; omega) (by rw [hml]; omega))
    fun u₃ ⟨b₃, g₃, s₃, d₃⟩ => ?_)
  -- The selection.
  have g26₃ : u₃.gpr .s8 = BitVec.ofNat 64 Ln := by rw [g₃ _ (by decide), o₂.get .s8, g26]
  have g25₃ : u₃.gpr .s11 = BitVec.ofNat 64 sl := by
    rw [g₃ _ (by decide), o₂.get .s11, k₁.get .s11, I.g _ (by decide), h25]
  refine WP.seq (WP.mono (select_ok L hD b₃ g26₃ g25₃ (by omega) (by omega)) fun u₄ ⟨b₄, k₄, v₄⟩ => ?_)
  -- The state back.
  refine WP.seq (WP.mono (copyN_ok L b₄ (a := oBk) (b := oSt) (n := H.S) hS0
    hHS (by omega) (by omega) (.inr (by omega)) (by decide) (by decide)) fun u₅ ⟨b₅, k₅, v₅⟩ => ?_)
  have s₄ : Same (Sp s) u₃ u₄ [(oSel, H.D)] := fun o ho hr => by
    have := hr _ (List.mem_singleton_self _)
    rw [v₄ o ho, ifn (by simp only at this; omega)]
  have s₅ : Same (Sp s) u₄ u₅ [(oSt, H.S)] := same_of_if v₅
  have r₅ : hH.SH.Repr u₅.mem (off (Sp s) oSt) m :=
    hH.congr u.mem u₅.mem _ _ (fun i hi => by
      have e := v₅ (oSt + i) (by omega)
      rw [ifp ⟨by omega, by omega⟩, show oBk + (oSt + i - oSt) = oBk + i by omega,
        s₄ (oBk + i) (by omega) (fun p hp => by simp at hp; subst hp; omega),
        s₃ (oBk + i) (by omega) (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> simp only <;> omega),
        show view u₂.mem (Sp s) (oBk + i) = view u₁.mem (Sp s) (oBk + i) by rw [o₂.mem], v₁ (oBk + i) (by omega),
        ifp ⟨by omega, by omega⟩, show oSt + (oBk + i - oBk) = oSt + i by omega] at e
      simp only [view] at e
      show u₅.mem (off (off (Sp s) oSt) i) = u.mem (off (off (Sp s) oSt) i)
      rw [off_off]; exact e) I.repr
  -- `update` with the next byte.
  refine WP.seq (wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun u₆ o₆ e₆ => ?_)
  refine wp_yBase (by rw [o₆.get .s0, b₅.s0]) fun u₇ o₇ e₇ =>
    wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun u₇' o₇' e₇' => wp_add fun u₈ o₈ e₈ =>
    wp_li (imm := 1) (by decide) fun u₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.a1, .a2, .a3] u₅ u₉ := (o₆.trans (o₇.trans (o₇'.trans (o₈.trans o₉)))).mono
  have b₉ := b₅.only F k₉
  have g26₅ : u₅.gpr .s8 = BitVec.ofNat 64 Ln := by
    rw [k₅.get .s8, k₄.get .s8, g26₃]
  have s₉ : Same (Sp s) t₀ u₉ (wrA H) :=
    ((((((I.same.trans (s₁.mono (by simp))).trans (Same.of_mem o₂.mem _)).trans (s₃.mono (by simp))).trans
      (s₄.mono (by simp))).trans (s₅.mono (by simp))).trans (Same.of_mem k₉.mem _))
  have hby : Spec.Sha256.bytesAt u₉.mem (off (Sp s) (oY + 8 + D + Ln)) 1 =
      Spec.Sha256.bytesAt t₀.mem (off (Sp s) oY + BitVec.ofNat 64 (8 + D + Ln)) 1 := by
    show _ = Spec.Sha256.bytesAt t₀.mem (off (off (Sp s) oY) (8 + D + Ln)) 1
    rw [bytes_same s₉ (by omega) (by simp; omega), off_off,
      show oY + (8 + D + Ln) = oY + 8 + D + Ln by omega]
  refine WP.seq (WP.mono (hUpd_ok F hH hF b₉ (m := m) (by rw [k₉.mem]; exact r₅)
    (by rw [o₉.get .a1, o₈.get .a1, o₇'.get .a1, o₇.get .a1, e₆, g26₅, ← BitVec.ofNat_add, hml, hD]
        congr 1; omega)
    (d := oY + 8 + D + Ln) (len := 1)
    (by rw [o₉.get .a2, e₈, e₇', e₇, o₇'.get .s8, o₇.get .s8, o₆.get .s8, g26₅, hD]
        show off (off (off (Sp s) oY) (8 + D)) Ln = _
        rw [off_off, off_off, show oY + (8 + D + Ln) = oY + 8 + D + Ln by omega])
    (by rw [e₉]) (by omega) (by omega)) fun w₁ ⟨c₁, h₁, t₁, q₁⟩ => ?_)
  refine wp_addi (imm := 1) fun w₂ p₂ f₂ => wp_subi (imm := 1) fun w p f => wp_nil ?_
  have kw : Only [.s8, .s9] w₁ w := (p₂.trans p).mono
  refine ⟨⟨c₁.only F kw, fun r hr => ?_, ?_, ?_, ?_, fun hs i hi => ?_⟩, ?_⟩
  · rw [kw.gpr r (by revert r; decide), h₁ r (by revert r; decide), k₉.gpr r (by revert r; decide),
      k₅.gpr r (by revert r; decide), k₄.gpr r (by revert r; decide), g₃ r (by revert r; decide),
      o₂.gpr r (by revert r; decide), k₁.gpr r (by revert r; decide), I.g r hr]
  · rw [p.get .s8, f₂, h₁ _ (by decide), k₉.get .s8, g26₅, ← BitVec.ofNat_add]
  · rw [kw.mem]
    show hH.SH.Repr w₁.mem _ (Spec.Sha256.bytesAt t₀.mem (off (Sp s) oY) (8 + D + (Ln + 1)))
    rw [show 8 + D + (Ln + 1) = 8 + D + Ln + 1 by omega, bytesAt_succ, ← hby]
    exact q₁
  · exact (s₉.trans (t₁.mono (by simp))).trans (Same.of_mem kw.mem _)
  · have hw : ∀ i < D, view w.mem (Sp s) (oSel + i) = view u₄.mem (Sp s) (oSel + i) := fun i hi => by
      rw [show view w.mem (Sp s) (oSel + i) = view w₁.mem (Sp s) (oSel + i) by rw [kw.mem],
        t₁ _ (by omega) (fun p hp => by simp at hp; subst hp; omega),
        show view u₉.mem (Sp s) (oSel + i) = view u₅.mem (Sp s) (oSel + i) by rw [k₉.mem],
        s₅ _ (by omega) (fun p hp => by simp at hp; subst hp; omega)]
    rw [hw i hi, v₄ _ (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [ifn (fun h' => by omega), s₃ _ (by omega) (fun p hp => by
        simp at hp; rcases hp with rfl | rfl <;> simp only <;> omega),
        show view u₂.mem (Sp s) (oSel + i) = view u₁.mem (Sp s) (oSel + i) by rw [o₂.mem],
        s₁ _ (by omega) (fun p hp => by simp at hp; subst hp; omega)]
      exact I.sel hs i hi
    · rw [ifp ⟨by omega, by omega, rfl⟩, show oDig + (oSel + i - oSel) = oDig + i by omega]
      have := congrArg (·.getD i 0) d₃
      simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show i < H.D by omega), Option.map_some, Option.getD_some] at this
      rw [view, ← off_off, this, List.getD_eq_getElem?_getD]
  · rw [f, p₂.get .s9, h₁ _ (by decide), k₉.get .s9, k₅.get .s9, k₄.get .s9, g₃ _ (by decide),
      o₂.get .s9, k₁.get .s9]

theorem hashAny_ok (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) {sl : Nat} (hsl : sl < dN)
    (h25 : t.gpr .s11 = BitVec.ofNat 64 sl) :
    WP isa (hashAny H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ kpA, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' (wrA H) ∧
      ∀ i < D, view t'.mem (Sp s) (oSel + i) = (hH.SH.H.hash (mB t.mem (Sp s) (8 + D + sl))).getD i 0 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  have hY : oY = 2048 := rfl
  have hB : oBk = 1376 := rfl
  have hS : oSel = 1568 := rfl
  refine WP.seq (WP.mono (hInit_ok F hH hF h) fun t₁ ⟨b₁, g₁, s₁, r₁⟩ => ?_)
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ => ?_)
  refine wp_yBase (by rw [o₂.get .s0, b₁.s0]) fun t₃ o₃ e₃ =>
    wp_li (imm := 8 + H.D) (by rw [hD]; omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.a1, .a2, .a3] t₁ t₄ := (o₂.trans (o₃.trans o₄)).mono
  refine WP.seq (WP.mono (hUpd_ok F hH hF (b₁.only F k₄) (m := []) (by rw [k₄.mem]; exact r₁)
    (by rw [o₄.get .a1, o₃.get .a1, e₂]; rfl) (d := oY) (len := 8 + D) (by rw [o₄.get .a2, e₃])
    (by rw [e₄, hD]) (Nat.le_refl _) (by omega)) fun t₅ ⟨b₅, g₅, s₅, r₅⟩ => ?_)
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.s8, .s9] t₅ t₇ := (o₆.trans o₇).mono
  have st : Same (Sp s) t t₇ (wrA H) :=
    (((s₁.mono (by simp)).trans (Same.of_mem k₄.mem _)).trans (s₅.mono (by simp))).trans (Same.of_mem k₇.mem _)
  have gk : ∀ r ∈ kpA, t₇.gpr r = t.gpr r := fun r hr => by
    rw [k₇.gpr r (by revert r; decide), g₅ r (by revert r; decide), k₄.gpr r (by revert r; decide),
      g₁ r (by revert r; decide)]
  have hmB : ∀ n ≤ 2048, mB t₇.mem (Sp s) n = mB t.mem (Sp s) n := fun n hn =>
    bytes_same st (by omega) (by simp; omega)
  have I0 : AnyI hH D s t₇ sl 0 t₇ := by
    refine ⟨b₅.only F k₇, fun _ _ => rfl, by rw [o₇.get .s8, e₆], ?_, Same.refl _ _ _,
      fun h' => absurd h' (Nat.not_lt_zero _)⟩
    rw [k₇.mem, Nat.add_zero, mB, bytes_same s₅ (d := oY) (n := 8 + D) (by omega) (by simp; omega)]
    simpa using r₅
  refine WP.mono (wp_countdown (cnt := .s9) (N := dN) (by omega) (by omega) (AnyI hH D s t₇ sl)
    (fun Ln hL u I _ => lenRound_ok L hH hF hD hsl (by rw [gk _ (by decide), h25]) hL I) I0
    (by rw [e₇, o₆.get .s4, b₅.pdb, L.hdb])) fun u I => ⟨I.base, fun r hr => by rw [I.g r hr, gk r hr],
      st.trans (I.same.mono (by simp)), fun i hi => by rw [I.sel hsl i hi, hmB _ (by omega)]⟩

end

end VG.Proof.RsaPss.RISCV64


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
    WP isa (.block (([.li .t5 8] : List Instr) ++ is)) u Q :=
  wp_li (imm := 8) (by decide) k

/-- `t5 := 2048`. -/
theorem nset2048 {u : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Only [.t5] u u' → u'.gpr .t5 = BitVec.ofNat 64 2048 → WP isa (.block is) u' Q) :
    WP isa (.block (([.li .t5 1024, .shift .sll .d .t5 .t5 1] : List Instr) ++ is)) u Q :=
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
