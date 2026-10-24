module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: `H'` for any salt length

Untrusted: everything here is checked by Lean. `hashAny_ok`: after
`0⁸ ‖ mHash`, for each length `L < dbLen` (`lenRound_ok`) the streaming state
is copied to `oBk`, finalized, its digest kept at `oSel` if `L` is the salt's
length `sl`, copied back and updated with the next byte of `M'`: the state
represents the first `8 + hLen + L` bytes of `M'` (`AnyI`), and after the
loop `oSel` holds the hash of the first `8 + hLen + sl`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- The first `n` bytes of `M'`. -/
abbrev mB (m : Mem) (S : Addr) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (off S oY) n

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    Spec.Sha256.bytesAt m p (n + 1) = Spec.Sha256.bytesAt m p n ++ Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 n) 1 := by
  simp [Spec.Sha256.bytesAt, List.range_succ]

theorem same_of_if {S : Addr} {t t' : State} {b n : Nat} {f : Nat → Byte}
    (h : ∀ o < oRsa, view t'.mem S o = if b ≤ o ∧ o < b + n then f o else view t.mem S o) : Same S t t' [(b, n)] :=
  fun o ho hr => by
    have := hr (b, n) (List.mem_singleton_self _)
    rw [h o ho, ifn (by simp only at this; omega)]

/-- The registers the loop keeps. -/
abbrev kpA : List Reg := Reg.r14 :: fx ++ hiRegs ++ ([.r24, .r25, .r28, .r29] : List Reg)

/-- The ranges the loop writes. -/
abbrev wrA (H : Hash) : List (Nat × Nat) := [(oSt, H.S), (oDig, H.FD), (oW, H.W), (oBk, H.S), (oSel, H.D)]

/-- After `L` lengths, from the state `t₀` before the loop. -/
structure AnyI {H : Hash} (hH : HashOK H) (D : Nat) (s t₀ : State) (sl L : Nat) (u : State) : Prop where
  base : Base Sp (vP D) s u
  g : ∀ r ∈ kpA, u.gpr r = t₀.gpr r
  r26 : u.gpr .r26 = BitVec.ofNat 64 L
  repr : hH.SH.Repr u.mem (off (Sp s) oSt) (mB t₀.mem (Sp s) (8 + D + L))
  same : Same (Sp s) t₀ u (wrA H)
  sel : sl < L → ∀ i < D, view u.mem (Sp s) (oSel + i) = (hH.SH.H.hash (mB t₀.mem (Sp s) (8 + D + sl))).getD i 0

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
include L hH

theorem lenRound_ok (hD : H.D = D) {t₀ : State} {sl Ln : Nat} (hsl : sl < dN) (h25 : t₀.gpr .r25 = BitVec.ofNat 64 sl)
    (hL : Ln < dN) {u : State} (I : AnyI hH D s t₀ sl Ln u) :
    WP isa (lenRound H) u fun u' => AnyI hH D s t₀ sl (Ln + 1) u' ∧ u'.gpr .r27 = u.gpr .r27 - BitVec.ofNat 64 1 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  have hB : oBk = 4608 := rfl
  have hS : oSel = 4800 := rfl
  have hHS : H.S < 2 ^ 15 := by omega
  let m := mB t₀.mem (Sp s) (8 + D + Ln)
  have hml : m.length = 8 + D + Ln := by simp [m, Spec.Sha256.bytesAt]
  -- The state to `oBk`.
  refine WP.seq (WP.mono (copyN_ok L I.base (a := oSt) (b := oBk) (n := H.S) (by have := hH.dims.N; simp only [Hash.S]; omega)
    hHS (by omega) (by omega) (.inl (by omega)) (by omega) (by decide)) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  have s₁ : Same (Sp s) u u₁ [(oBk, H.S)] := same_of_if v₁
  have r₁ : hH.SH.Repr u₁.mem (off (Sp s) oSt) m :=
    hH.congr u.mem u₁.mem _ _ (fun i hi => by
      have := s₁ (oSt + i) (by omega) (fun p hp => by simp at hp; subst hp; omega)
      simp only [view] at this; rw [← off_off] at this; exact this) I.repr
  -- `finalize`.
  refine WP.seq (wp_addi (h := by rw [hD]; omega) fun u₂ o₂ e₂ => wp_nil ?_)
  have b₂ := b₁.only F o₂
  have g26 : u₁.gpr .r26 = BitVec.ofNat 64 Ln := by rw [k₁.get .r26, I.r26]
  refine WP.seq (WP.mono (hFin_ok F hH b₂ (m := m) (by rw [o₂.mem]; exact r₁)
    (by rw [e₂, g26, ← BitVec.ofNat_add, hml, hD]; congr 1; omega) (by rw [hml]; omega))
    fun u₃ ⟨b₃, g₃, s₃, d₃⟩ => ?_)
  -- The selection.
  have g26₃ : u₃.gpr .r26 = BitVec.ofNat 64 Ln := by rw [g₃ _ (by decide), o₂.get .r26, g26]
  have g25₃ : u₃.gpr .r25 = BitVec.ofNat 64 sl := by
    rw [g₃ _ (by decide), o₂.get .r25, k₁.get .r25, I.g _ (by decide), h25]
  refine WP.seq (WP.mono (select_ok L hD b₃ g26₃ g25₃ (by omega) (by omega)) fun u₄ ⟨b₄, k₄, v₄⟩ => ?_)
  -- The state back.
  refine WP.seq (WP.mono (copyN_ok L b₄ (a := oBk) (b := oSt) (n := H.S) (by have := hH.dims.N; simp only [Hash.S]; omega)
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
        s₃ (oBk + i) (by omega) (fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> simp only <;> omega),
        show view u₂.mem (Sp s) (oBk + i) = view u₁.mem (Sp s) (oBk + i) by rw [o₂.mem], v₁ (oBk + i) (by omega),
        ifp ⟨by omega, by omega⟩, show oSt + (oBk + i - oBk) = oSt + i by omega] at e
      simp only [view] at e
      show u₅.mem (off (off (Sp s) oSt) i) = u.mem (off (off (Sp s) oSt) i)
      rw [off_off]; exact e) I.repr
  -- `update` with the next byte.
  refine WP.seq (wp_addi (h := by rw [hD]; omega) fun u₆ o₆ e₆ => wp_addi (h := by rw [hD]; unfold oY; omega)
    fun u₇ o₇ e₇ => wp_add fun u₈ o₈ e₈ => wp_li (by decide) fun u₉ o₉ e₉ => wp_nil ?_)
  have k₉ : Only [.r4, .r5, .r6] u₅ u₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only F k₉
  have g26₅ : u₅.gpr .r26 = BitVec.ofNat 64 Ln := by
    rw [k₅.get .r26, k₄.get .r26, g26₃]
  have s₉ : Same (Sp s) t₀ u₉ (wrA H) :=
    ((((((I.same.trans (s₁.mono (by simp))).trans (Same.of_mem o₂.mem _)).trans (s₃.mono (by simp))).trans
      (s₄.mono (by simp))).trans (s₅.mono (by simp))).trans (Same.of_mem k₉.mem _))
  have hby : Spec.Sha256.bytesAt u₉.mem (off (Sp s) (oY + 8 + D + Ln)) 1 =
      Spec.Sha256.bytesAt t₀.mem (off (Sp s) oY + BitVec.ofNat 64 (8 + D + Ln)) 1 := by
    show _ = Spec.Sha256.bytesAt t₀.mem (off (off (Sp s) oY) (8 + D + Ln)) 1
    rw [bytes_same s₉ (by omega) (by simp; omega), off_off, show oY + (8 + D + Ln) = oY + 8 + D + Ln by omega]
  refine WP.seq (WP.mono (hUpd_ok F hH b₉ (m := m) (by rw [k₉.mem]; exact r₅)
    (by rw [o₉.get .r4, o₈.get .r4, o₇.get .r4, e₆, g26₅, ← BitVec.ofNat_add, hml, hD]; congr 1; omega)
    (d := oY + 8 + D + Ln) (len := 1)
    (by rw [o₉.get .r5, e₈, e₇, o₇.get .r26, o₆.get .r14, o₆.get .r26, g26₅, b₅.r14, hD]; exact off_off _ _ _)
    (by rw [e₉]) (by omega) (by omega)) fun w₁ ⟨c₁, h₁, t₁, q₁⟩ => ?_)
  refine wp_addi fun w₂ p₂ f₂ => wp_subi fun w p f => wp_nil ?_
  have kw : Only [.r26, .r27] w₁ w := (p₂.trans p).mono
  refine ⟨⟨c₁.only F kw, fun r hr => ?_, ?_, ?_, ?_, fun hs i hi => ?_⟩, ?_⟩
  · rw [kw.gpr r (by revert r; decide), h₁ r (by revert r; decide), k₉.gpr r (by revert r; decide),
      k₅.gpr r (by revert r; decide), k₄.gpr r (by revert r; decide), g₃ r (by revert r; decide),
      o₂.gpr r (by revert r; decide), k₁.gpr r (by revert r; decide), I.g r hr]
  · rw [p.get .r26, f₂, h₁ _ (by decide), k₉.get .r26, g26₅, ← BitVec.ofNat_add]
  · rw [kw.mem]
    show hH.SH.Repr w₁.mem _ (Spec.Sha256.bytesAt t₀.mem (off (Sp s) oY) (8 + D + (Ln + 1)))
    rw [show 8 + D + (Ln + 1) = 8 + D + Ln + 1 by omega, bytesAt_succ, ← hby]
    exact q₁
  · exact (s₉.trans (t₁.mono (by simp))).trans (Same.of_mem kw.mem _)
  · have hw : ∀ i < D, view w.mem (Sp s) (oSel + i) = view u₄.mem (Sp s) (oSel + i) := fun i hi => by
      rw [show view w.mem (Sp s) (oSel + i) = view w₁.mem (Sp s) (oSel + i) by rw [kw.mem],
        t₁ _ (by omega) (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> simp only <;> omega),
        show view u₉.mem (Sp s) (oSel + i) = view u₅.mem (Sp s) (oSel + i) by rw [k₉.mem],
        s₅ _ (by omega) (fun p hp => by simp at hp; subst hp; omega)]
    rw [hw i hi, v₄ _ (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [ifn (fun h' => by omega), s₃ _ (by omega) (fun p hp => by
        simp at hp; rcases hp with rfl | rfl | rfl <;> simp only <;> omega),
        show view u₂.mem (Sp s) (oSel + i) = view u₁.mem (Sp s) (oSel + i) by rw [o₂.mem],
        s₁ _ (by omega) (fun p hp => by simp at hp; subst hp; omega)]
      exact I.sel hs i hi
    · rw [ifp ⟨by omega, by omega, rfl⟩, show oDig + (oSel + i - oSel) = oDig + i by omega]
      have := congrArg (·.getD i 0) d₃
      simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show i < H.FD by have := hH.hDF; omega), Option.map_some, Option.getD_some] at this
      rw [view, ← off_off, this, hH.hashTake, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
        ← List.getD_eq_getElem?_getD]
  · rw [f, p₂.get .r27, h₁ _ (by decide), k₉.get .r27, k₅.get .r27, k₄.get .r27, g₃ _ (by decide),
      o₂.get .r27, k₁.get .r27]

theorem hashAny_ok (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) {sl : Nat} (hsl : sl < dN)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa (hashAny H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ kpA, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' (wrA H) ∧
      ∀ i < D, view t'.mem (Sp s) (oSel + i) = (hH.SH.H.hash (mB t.mem (Sp s) (8 + D + sl))).getD i 0 := by
  have F := L.F
  have Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  have hY : oY = 2560 := rfl
  have hB : oBk = 4608 := rfl
  have hS : oSel = 4800 := rfl
  refine WP.seq (WP.mono (hInit_ok F hH h) fun t₁ ⟨b₁, g₁, s₁, r₁⟩ => ?_)
  refine WP.seq (wp_li (by decide) fun t₂ o₂ e₂ => wp_addi (h := by decide) fun t₃ o₃ e₃ =>
    wp_li (by rw [hD]; omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r6] t₁ t₄ := (o₂.trans (o₃.trans o₄)).mono
  refine WP.seq (WP.mono (hUpd_ok F hH (b₁.only F k₄) (m := []) (by rw [k₄.mem]; exact r₁)
    (by rw [o₄.get .r4, o₃.get .r4, e₂]; rfl) (d := oY) (len := 8 + D) (by rw [o₄.get .r5, e₃, o₂.get .r14, b₁.r14])
    (by rw [e₄, hD]) (Nat.le_refl _) (by unfold oRsa; omega)) fun t₅ ⟨b₅, g₅, s₅, r₅⟩ => ?_)
  refine WP.seq (wp_li (by decide) fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r26, .r27] t₅ t₇ := (o₆.trans o₇).mono
  have st : Same (Sp s) t t₇ (wrA H) :=
    (((s₁.mono (by simp)).trans (Same.of_mem k₄.mem _)).trans (s₅.mono (by simp))).trans (Same.of_mem k₇.mem _)
  have gk : ∀ r ∈ kpA, t₇.gpr r = t.gpr r := fun r hr => by
    rw [k₇.gpr r (by revert r; decide), g₅ r (by revert r; decide), k₄.gpr r (by revert r; decide),
      g₁ r (by revert r; decide)]
  have hmB : ∀ n ≤ 2048, mB t₇.mem (Sp s) n = mB t.mem (Sp s) n := fun n hn =>
    bytes_same st (by unfold oRsa; omega) (by simp; omega)
  have I0 : AnyI hH D s t₇ sl 0 t₇ := by
    refine ⟨b₅.only F k₇, fun _ _ => rfl, by rw [o₇.get .r26, e₆], ?_, Same.refl _ _ _, fun h' => absurd h' (Nat.not_lt_zero _)⟩
    rw [k₇.mem, Nat.add_zero, mB, bytes_same s₅ (d := oY) (n := 8 + D) (by unfold oRsa; omega) (by simp; omega)]
    simpa using r₅
  refine WP.mono (wp_countdown (cnt := .r27) (N := dN) (by omega) (by omega) (AnyI hH D s t₇ sl) (fun Ln hL u I _ =>
    lenRound_ok L hH hD hsl (by rw [gk _ (by decide), h25]) hL I) I0
    (by rw [e₇, o₆.get .r21, b₅.pdb, L.hdb])) fun u I => ⟨I.base, fun r hr => by rw [I.g r hr, gk r hr],
      st.trans (I.same.mono (by simp)), fun i hi => by rw [I.sel hsl i hi, hmB _ (by omega)]⟩

end

end VG.Proof.RsaPss.PPC64LE
