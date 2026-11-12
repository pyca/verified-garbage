module
public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
public import VerifiedGarbage.Proof.Rsa.AArch64.CkPhaseCore
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop
public import VerifiedGarbage.Proof.Rsa.AArch64.WDiv

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.KeyBounds
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_check_key` on AArch64: the phases of `main`

`KS c`: `CkS`, the mask `c`, and `n`, `e` and 1 in their arrays. Each phase
of the checks and'es its conditions into the mask (`phDN_ok`, `phPQ_ok`,
`phMod_ok`, `phQIC_ok`), exactly when the facts the key's other checks give
hold.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG.Impl.Rsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The full-exponent quotient count comes from the other factor's length. -/
theorem topD_ok {B : Addr} {Z sl : Nat} {m₀ : Mem} {yl : Nat} (hsl : sl < 32)
    (hy : word m₀ B (8 * sl) = BitVec.ofNat 64 yl) (hyl : yl < 2 ^ 32) (hZ : 8 * 32 ≤ Z) :
    TopOk (topD sl) B Z m₀ ((yl + 7) / 8 + 1) := fun t hs h0 hh => by
  have hl := hs.ld (d := 8 * sl) (by omega_arith)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((yl + 7) / 8 + 1) ∧
    t'.mem = t.mem ∧ t'.c = t.c) ?_ (by rfl) (by rfl) (by rfl)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topD
  brun [hdr_enc hsl, h0, hl, hh sl hsl, hy, BitVec.ofNat_add_ofNat, shr_ofNat (show yl + 7 < 2 ^ 64 by omega_arith)]

/-! ## `wmodOne`: the remainder by words when `wordGuard` passes -/

/-- `wM`: `w_m = (W - 2) / 4`. -/
theorem ckWm_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) : WmOk wM w ((w - 2) / 4) := fun t h12 => by
  refine WP.keep [.x12] (Q := fun t' => t'.gpr .x12 = BitVec.ofNat 64 ((w - 2) / 4) ∧ t'.mem = t.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  unfold wM
  brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith)]

/-- `L = W / 2` words of `e d`. -/
theorem ckLenD_ok (w : Nat) (hw : w < 2 ^ 24) : LenOk lenD w (w / 2) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 (w / 2) ∧ t'.mem = t.mem)
    (by unfold lenD; brun [h12, shr_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide) (by decide) (by decide +kernel)

/-- `L = w_m + 1` words of `e dX`. -/
theorem ckLenE_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) :
    LenOk lenE w ((w - 2) / 4 + 1) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((w - 2) / 4 + 1) ∧ t'.mem = t.mem)
    (by unfold lenE; brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith),
      BitVec.ofNat_add_ofNat]) (by decide) (by decide) (by decide +kernel)

/-- `L = 2 w_m` words of `q qInv`. -/
theorem ckLenQ_ok (w : Nat) (hw2 : 2 ≤ w) (hw : w < 2 ^ 24) :
    LenOk lenQ w ((w - 2) / 2) := fun t h12 =>
  WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((w - 2) / 2) ∧ t'.mem = t.mem)
    (by unfold lenQ; brun [h12, bv_sub_ofNat hw2 (by omega_arith), shr_ofNat (show w - 2 < 2 ^ 64 by omega_arith)])
    (by decide) (by decide) (by decide +kernel)

/-- `aBase`: `[aA]`'s word `-1`, an array below `[aRem]`, for `W = 4 w_m + 2`. -/
theorem ckXb_ok (B : Addr) (w : Nat) (hw : w % 4 = 2) (hw' : w < 2 ^ 24) :
    XbOk aBase B (slot w aRem) (slot w aA) ((w - 2) / 4) := fun t h11 h12 => by
  have e : off B (slot w aA - 8) + BitVec.ofNat 64 (32 * ((w - 2) / 4) + 40) = off B (slot w aRem) := by
    rw [off_add]; congr 1; simp only [slot, aA, aRem]; omega_arith
  refine WP.keep [.x16] (Q := fun t' => t'.gpr .x16 = off B (slot w aA - 8) ∧ t'.mem = t.mem)
    ?_ (by decide) (by decide) (by decide +kernel)
  unfold aBase
  brun [h11, h12, shl5_ofNat (show (w - 2) / 4 < 2 ^ 58 by omega_arith)]
  rw [← e, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

/-- The guard and its two paths: `[aRem] := [aA] mod [aM]`, when the words
of `[aA]` from `c` up are below `[aM]` and, if `wordGuard` passes, `[aA]`
fits in `L` words and `[aM]` in `w_m = k / 16` with its top bit set. -/
theorem ckWRem_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    {top : List Instr} {c : Nat} (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hcw : c < wW I.cap)
    {lenL : List Instr} {Ln : Nat} (hL : LenOk lenL (wW I.cap) Ln) (hLW : Ln ≤ wW I.cap) (hmL : wk I.k / 2 ≤ Ln) :
    WP isa (.seq (.block (wordGuard sPlen sQlen)) (.ite (.zero .x .x9) (wdiv aA aM aRem CheckKey.aT wM lenL aBase)
      (seqs (CheckCrtKey.reduceTop top)))) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM →
        (I.Gd → I.av s.mem aA < 2 ^ (64 * Ln) ∧ 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s.mem aM ∧
          I.av s.mem aM < 2 ^ (64 * (wk I.k / 2))) →
        I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aRem → i ≠ CheckCrtKey.aQ → i ≠ CheckKey.aT → I.av t.mem i = I.av s.mem i := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hpl := L.pl2
  have hql := L.ql2
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hn0 : 0 < I.nb.length := by rw [L.nl]; omega_arith
  refine WP.seq (WP.mono (wordGuard_ok (b := s.mem.read I.pN 1) h.ws.scr h.ws.x0 h256 (by decide) (by decide)
    h.args.k h.args.pl h.args.ql h.args.n rfl (by simpa using h.n.rd 0 hn0)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have h₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  have e₁ : ∀ i, I.av s₁.mem i = I.av s.mem i := fun i => by unfold CkIn.av; rw [m₁]
  refine WP.ite (s₁.gpr .x9 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · -- The guard passes: `wdiv`.
    have hg : guardVal I.k I.pl I.ql (s.mem.read I.pN 1) = 0 := by
      rw [← h9]; simpa using hb
    obtain ⟨g16, g2, gpq, gb⟩ := guard_zero (by omega_arith) (by omega_arith) (by omega_arith) hg
    have hb0 : 128 ≤ (I.nb[0]'hn0).toNat := by
      rw [read_one, show I.pN = I.pN + BitVec.ofNat 64 0 by simp, h.n.val 0 hn0] at gb; exact gb
    have hGd : I.Gd := ⟨g16, g2, gpq, hn0, hb0⟩
    have eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
    have hw8 : 8 ≤ wk I.k := by unfold wk; omega_arith
    have hwk : wk I.k % 2 = 0 := by unfold wk; omega_arith
    have hwm : (wW I.cap - 2) / 4 = wk I.k / 2 := by rw [eW]; omega_arith
    have hW := ckWm_ok (wW I.cap) (by omega_arith) (by rw [eW]; unfold wk; omega_arith)
    have hxb := ckXb_ok I.B (wW I.cap) (by rw [eW]; omega_arith) (by rw [eW]; unfold wk; omega_arith)
    rw [hwm] at hW hxb
    refine WP.mono (wdiv_ok h₁.ws (iX := aA) (iM := aM) (iR := aRem) (iT := CheckKey.aT) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hW hL hxb (by omega_arith)
      (by omega_arith) (by omega_arith) hmL) fun t ⟨_, ft, kt, hval⟩ => ?_
    have ht := h₁.step ft (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) kt (by decide)
    refine ⟨ht, ?_, fun _ hG => ?_, fun i hi h1 _ h3 => ?_⟩
    · show word t.mem I.B (8 * Public.sMask) = word s.mem I.B (8 * Public.sMask)
      rw [ft.word_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;>
          exact .inl (hdr_lt_slot _ _ (show Public.sMask < 32 by decide))) (by unfold Public.sMask sFn; omega_arith),
        m₁]
    · obtain ⟨hAL, hMlo, hMhi⟩ := hG hGd
      have hM0 : wv s₁.mem I.B (slot (wW I.cap) aM) (wk I.k / 2) = I.av s.mem aM := by
        have := e₁ aM
        unfold CkIn.av at this ⊢
        rw [wv_low_of_lt (v := wk I.k / 2) (w := wW I.cap) (by omega_arith) (by rw [this]; exact hMhi), this]
      have hA0 : wv s₁.mem I.B (slot (wW I.cap) aA) Ln = I.av s.mem aA := by
        have := e₁ aA
        unfold CkIn.av at this ⊢
        rw [wv_low_of_lt (v := Ln) (w := wW I.cap) hLW (by rw [this]; exact hAL), this]
      have htop : 2 ^ 63 ≤ (word s₁.mem I.B (slot (wW I.cap) aM + 8 * (wk I.k / 2 - 1))).toNat := by
        rw [word_of_wv _ _ _ (wk I.k / 2) (by omega_arith), hM0]
        exact top_word_of (by omega_arith) hMlo hMhi
      have hv := hval htop
      rw [hM0, hA0] at hv
      have hM : 0 < I.av s.mem aM := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hMlo
      have hlt : wv t.mem I.B (slot (wW I.cap) aRem) (wW I.cap + 2) < 2 ^ (64 * wW I.cap) := by
        rw [hv]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
      unfold CkIn.av
      rw [wv_low_of_lt (by omega_arith) hlt, hv]
    · rw [← e₁ i]
      unfold CkIn.av
      exact ft.wv_eq (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := slot_sep (w := wW I.cap) h1; omega_arith
        · have := slot_sep (w := wW I.cap) h3; omega_arith) (by have := h.ws.sl hi; omega_arith)
  · -- `reduceTop`.
    refine WP.mono (ckReduceTop_ok h₁ (by rw [m₁]; exact hT) hc1 hcw) fun t ⟨ht, mt, vt, ot⟩ =>
      ⟨ht, by rw [mt, m₁], fun hlt _ => by rw [vt (by rw [e₁, e₁]; exact hlt), e₁, e₁],
        fun i hi a b d => by rw [ot i hi a b d, e₁]⟩

/-- `wmodOne`: the mask of `[aA] mod [aM] = 1`, under `ckWRem_ok`'s
conditions. -/
theorem ckWModOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    {g : Bool} (hm : mword s.mem I.B = mask g) (hO : I.av s.mem aOne = 1)
    {top : List Instr} {c : Nat} (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hcw : c < wW I.cap)
    {lenL : List Instr} {Ln : Nat} (hL : LenOk lenL (wW I.cap) Ln) (hLW : Ln ≤ wW I.cap) (hmL : wk I.k / 2 ≤ Ln) :
    WP isa (seqs (wmodOne top lenL)) s fun t => CkS I m₀ t ∧ (∃ r : Nat,
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM →
        (I.Gd → I.av s.mem aA < 2 ^ (64 * Ln) ∧ 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s.mem aM ∧
          I.av s.mem aM < 2 ^ (64 * (wk I.k / 2))) → r = I.av s.mem aA % I.av s.mem aM) ∧
      mword t.mem I.B = mask (decide (r = 1) && g)) ∧
      ∀ i < 16, i ≠ aRem → i ≠ CheckCrtKey.aQ → i ≠ CheckKey.aT → I.av t.mem i = I.av s.mem i := by
  unfold wmodOne
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (ckWRem_ok h L hT hc1 hcw hL hLW hmL)
    fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckEq_ok h₁ (a := aRem) (b := aOne) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  refine ⟨ht, ⟨I.av s₁.mem aRem, v₁, ?_⟩, fun i hi h1 h2 h3 => by rw [ot i hi, o₁ i hi h1 h2 h3]⟩
  rw [mt, o₁ aOne (by decide) (by decide) (by decide) (by decide), hO]

theorem modChecks_eq (sX sXlen sDX sYlen : Nat) : modChecks sX sXlen sDX sYlen =
    loadA aM sX sXlen ++ (([.block (decA aM)] : List (Prog isa)) ++ (loadA aX sDX sXlen ++ (ltA aX aM ++ (loadA aX sD sDlen ++
      (mulE ++ (wmodOne (topD sYlen) lenD ++ (loadA aX sDX sXlen ++ (mulE ++ wmodOne CheckCrtKey.topE lenE)))))))) := by
  simp only [modChecks, List.append_assoc]

/-- The checks modulo `X - 1`, for the prime `X` (the bytes `xb`) and its
exponent `dX` (the bytes `dxb`). -/
theorem phMod_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) (hE64 : I.E < 2 ^ 64)
    {sX sXlen sDX xl : Nat} {pX pDX : Addr} {xb dxb : List Byte} (hsX : sX < 32) (hsL : sXlen < 32)
    (hsD : sDX < 32) (hxl1 : 1 ≤ xl) (hxl2 : xl < I.k) (hxc : xl ≤ I.cap) (hxb : xb.length = xl) (hdxb : dxb.length = xl)
    (hA : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sX) = pX ∧ word t.mem I.B (8 * sXlen) = BitVec.ofNat 64 xl ∧
      Src t I.B I.Z pX xb ∧ word t.mem I.B (8 * sDX) = pDX ∧ Src t I.B I.Z pDX dxb)
    {sYlen yl Y : Nat} (hsY : sYlen < 32) (hyc : yl ≤ I.cap)
    (hY : ∀ t, CkS I m₀ t → word t.mem I.B (8 * sYlen) = BitVec.ofNat 64 yl)
    (hy : Y < 2 ^ (64 * ((yl + 7) / 8))) (he33 : I.E < 2 ^ 33)
    (hXg : I.Gd → Spec.Rsa.os2ip xb * Y = I.N →
      2 ^ (64 * (wk I.k / 2) - 1) ≤ Spec.Rsa.os2ip xb - 1 ∧ Spec.Rsa.os2ip xb < 2 ^ (64 * (wk I.k / 2))) :
    WP isa (seqs (modChecks sX sXlen sDX sYlen)) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (Spec.Rsa.os2ip xb % 2 = 1 → 1 < Spec.Rsa.os2ip xb → I.D < I.N → Spec.Rsa.os2ip xb * Y = I.N →
        g = (decide (Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1) &&
          decide (I.D * I.E % (Spec.Rsa.os2ip xb - 1) = 1) &&
          decide (I.E * Spec.Rsa.os2ip dxb % (Spec.Rsa.os2ip xb - 1) = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  have k1 := L.k1
  have k2 := L.k2
  have eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
  have hwk : wk I.k < 2 ^ 20 := by unfold wk; omega_arith
  rw [modChecks_eq]
  -- `[aM] := X - 1`.
  obtain ⟨a1, a2, a3, -, -⟩ := hA s hs
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (ckLoad_ok hs (j := aM) (by decide) hsX hsL a1 a2 a3
    hxb hxl1 (Nat.le_of_lt hxl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (a := [.block (decA aM)]) (by simp) (by simp [loadA]) (WP.mono (ckDec_ok h₁)
    fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  rw [v₁] at v₂
  -- `dX < X - 1`.
  obtain ⟨-, b2, -, b4, b5⟩ := hA s₂ h₂
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₂ (j := aX) (by decide) hsD hsL b4
    b2 b5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  have M₃ : I.av s₃.mem aM = I.av s₂.mem aM := o₃ aM (by decide) (by decide)
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₃ (a := aX) (b := aM) (by decide)
    (by decide) (m₃.trans (m₂.trans (m₁.trans hm)))) fun s₄ ⟨h₄, m₄, o₄⟩ => ?_)
  rw [v₃, M₃] at m₄
  -- `d e mod (X - 1) = 1`.
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₄ (j := aX) (by decide) (by decide)
    (by decide) h₄.args.d h₄.args.dl h₄.d L.dbl L.dl1 L.dl2) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  have E₅ : I.av s₅.mem aE = I.E := by
    rw [o₅ aE (by decide) (by decide), o₄ aE (by decide), o₃ aE (by decide) (by decide), o₂ aE (by decide) (by decide),
      o₁ aE (by decide) (by decide), hE]
  refine wp_seqs_append (by simp [mulE]) (by simp [wmodOne]) (WP.mono (ckMulE_ok h₅ L
    (by rw [v₅]; exact lt_w (by rw [L.dbl]; exact L.dcap))) fun s₆ ⟨h₆, m₆, v₆, o₆⟩ => ?_)
  rw [v₅, e_word E₅ hE64] at v₆
  have O₆ : I.av s₆.mem aOne = 1 := by
    rw [o₆ aOne (by decide) (by decide), o₅ aOne (by decide) (by decide), o₄ aOne (by decide),
      o₃ aOne (by decide) (by decide), o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  refine wp_seqs_append (by simp [wmodOne]) (by simp [loadA]) (WP.mono (ckWModOne_ok h₆ L
    (m₆.trans (m₅.trans m₄)) O₆ (topD_ok hsY (hY _ h₆) (by have := L.cap2; have := L.k2; omega_arith)
      h₆.ws.h256) (by omega_arith)
    (by have := L.cap1; unfold wW wk; omega_arith) (ckLenD_ok (wW I.cap) (by rw [eW]; omega_arith))
    (by omega_arith) (by rw [eW]; omega_arith)) fun s₇ ⟨h₇, ⟨r₁, hr₁, m₇⟩, o₇⟩ => ?_)
  have M₆ : I.av s₆.mem aM = I.av s₂.mem aM := by
    rw [o₆ aM (by decide) (by decide), o₅ aM (by decide) (by decide), o₄ aM (by decide), M₃]
  rw [v₆, M₆] at hr₁
  -- `e dX mod (X - 1) = 1`.
  obtain ⟨-, -, -, c4, c5⟩ := hA s₇ h₇
  refine wp_seqs_append (by simp [loadA]) (by simp [mulE]) (WP.mono (ckLoad_ok h₇ (j := aX) (by decide) hsD hsL c4
    ((hA s₇ h₇).2.1) c5 hdxb hxl1 (Nat.le_of_lt hxl2)) fun s₈ ⟨h₈, m₈, v₈, o₈⟩ => ?_)
  have E₈ : I.av s₈.mem aE = I.E := by
    rw [o₈ aE (by decide) (by decide), o₇ aE (by decide) (by decide) (by decide) (by decide), o₆ aE (by decide)
      (by decide), E₅]
  refine wp_seqs_append (by simp [mulE]) (by simp [wmodOne]) (WP.mono (ckMulE_ok h₈ L
    (by rw [v₈]; exact lt_w (by rw [hdxb]; exact hxc))) fun s₉ ⟨h₉, m₉, v₉, o₉⟩ => ?_)
  rw [v₈, e_word E₈ hE64] at v₉
  have O₉ : I.av s₉.mem aOne = 1 := by
    rw [o₉ aOne (by decide) (by decide), o₈ aOne (by decide) (by decide),
      o₇ aOne (by decide) (by decide) (by decide) (by decide), O₆]
  refine WP.mono (ckWModOne_ok h₉ L (m₉.trans (m₈.trans m₇)) O₉ (topE_ok _ _ _)
    (by omega_arith) (by unfold wW; omega_arith) (ckLenE_ok (wW I.cap) (by omega_arith) (by rw [eW]; omega_arith))
    (by rw [eW]; omega_arith) (by rw [eW]; omega_arith)) fun t ⟨ht, ⟨r₂, hr₂, mt⟩, ot⟩ => ?_
  have M₉ : I.av s₉.mem aM = I.av s₂.mem aM := by
    rw [o₉ aM (by decide) (by decide), o₈ aM (by decide) (by decide), o₇ aM (by decide) (by decide) (by decide)
      (by decide), M₆]
  rw [v₉, M₉] at hr₂
  -- What the other arrays keep.
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    have d6 : i ≠ CheckCrtKey.aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d6 d5, o₉ i h16 d3, o₈ i h16 d2, o₇ i h16 d4 d6 d5, o₆ i h16 d3, o₅ i h16 d2, o₄ i h16,
      o₃ i h16 d2, o₂ i h16 d1, o₁ i h16 d1]
  refine ⟨decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) && decide (r₁ = 1) && decide (r₂ = 1), ⟨ht, ?_,
    by rw [keep 0 (.inl rfl), hN], by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩,
    fun ho h1 hd hpq => ?_⟩
  · rw [mt]
    cases decide (r₂ = 1) <;> cases decide (r₁ = 1) <;> cases decide (Spec.Rsa.os2ip dxb < I.av s₂.mem aM) <;>
      cases c <;> rfl
  · have hM : I.av s₂.mem aM = Spec.Rsa.os2ip xb - 1 := v₂ ho
    have hM0 : 0 < I.av s₂.mem aM := by rw [hM]; omega_arith
    have hdBound : I.D * I.E / 2 ^ (64 * ((yl + 7) / 8 + 1)) < I.av s₂.mem aM := by
      rw [hM, Nat.mul_comm I.D I.E]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        (by rw [Nat.mul_comm (Spec.Rsa.os2ip xb - 1)]; exact Proof.Rsa.fullExp_bound (x := Spec.Rsa.os2ip xb) (L := yl) he33 (by omega_arith) (by rw [hpq]; exact hd) hy)
    have hN : I.N < 2 ^ (64 * wk I.k) := lt_w (by rw [L.nl])
    have gM : I.Gd → 2 ^ (64 * (wk I.k / 2) - 1) ≤ I.av s₂.mem aM ∧ I.av s₂.mem aM < 2 ^ (64 * (wk I.k / 2)) :=
      fun hG => by
        obtain ⟨g1, g2⟩ := hXg hG hpq
        rw [hM]; exact ⟨g1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) g2⟩
    rw [hr₁ hdBound (fun hG => ⟨?_, gM hG⟩), hM]
    · by_cases hlt : Spec.Rsa.os2ip dxb < Spec.Rsa.os2ip xb - 1
      · rw [hr₂ (by rw [hM]; exact Nat.lt_of_le_of_lt (mul_div_top_le (k := 1) (by simpa using hE64)) hlt)
          (fun hG => ⟨?_, gM hG⟩), hM, Nat.mul_comm (Spec.Rsa.os2ip dxb) I.E]
        -- `e dX < 2^64 · 2^(64 w_m)`.
        have hX := (gM hG).2
        rw [hM] at hX
        rw [eW, show (2 * wk I.k + 2 - 2) / 4 + 1 = wk I.k / 2 + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_trans hlt (by omega_arith)) (Nat.le_of_lt (by simpa using hE64))
          (Nat.two_pow_pos _)
      · simp only [hlt, decide_false, Bool.false_and]
    · -- `d e < 2^(64 (w + 1))`.
      rw [eW, show (2 * wk I.k + 2) / 2 = wk I.k + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_trans hd hN) (Nat.le_of_lt (by simpa using hE64)) (Nat.two_pow_pos _)


/-- `qInv < p` and `q qInv ≡ 1 (mod p)`, by `wmodOne`. -/
theorem phQIC_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I)
    (hPg : I.Gd → I.P * I.Q = I.N →
      2 ^ (64 * (wk I.k / 2) - 1) ≤ I.P - 1 ∧ I.P < 2 ^ (64 * (wk I.k / 2))) :
    WP isa (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++ (loadA aR sQ sQlen ++
      (mulPQ ++ wmodOne CheckCrtKey.topQ lenQ)))))) s fun t => ∃ g : Bool, KS I m₀ (g && c) t ∧
      (0 < I.P → I.P * I.Q = I.N → g = (decide (I.QI < I.P) && decide (I.Q * I.QI % I.P = 1))) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  have eW : wW I.cap = 2 * wk I.k + 2 := by rw [L.capk]
  have k2 := L.k2
  have hwk : wk I.k < 2 ^ 20 := by unfold wk; omega_arith
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aM) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok h₁ (j := aX) (by decide) (by decide)
    (by decide) h₁.args.qi h₁.args.pl h₁.qi L.qibl L.pl1 (Nat.le_of_lt L.pl2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have M₂ : I.av s₂.mem aM = I.P := by rw [o₂ aM (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [ltA]) (by simp [loadA]) (WP.mono (ckLt_ok h₂ (a := aX) (b := aM) (by decide)
    (by decide) (m₂.trans (m₁.trans hm))) fun s₃ ⟨h₃, m₃, o₃⟩ => ?_)
  rw [v₂, M₂] at m₃
  refine wp_seqs_append (by simp [loadA]) (by simp [mulPQ]) (WP.mono (ckLoad_ok h₃ (j := aR) (by decide) (by decide)
    (by decide) h₃.args.q h₃.args.ql h₃.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₄ ⟨h₄, m₄, v₄, o₄⟩ => ?_)
  have X₄ : I.av s₄.mem aX = I.QI := by rw [o₄ aX (by decide) (by decide), o₃ aX (by decide), v₂]
  refine wp_seqs_append (by simp [mulPQ]) (by simp [wmodOne]) (WP.mono (ckMulPQ_ok h₄ L
    (by rw [X₄]; have := os2ip_lt I.qib; rw [L.qibl] at this; exact this)
    (by rw [v₄]; have := os2ip_lt I.qb; rw [L.qbl] at this; exact this)) fun s₅ ⟨h₅, m₅, v₅, o₅⟩ => ?_)
  rw [X₄, v₄] at v₅
  have O₅ : I.av s₅.mem aOne = 1 := by
    rw [o₅ aOne (by decide) (by decide), o₄ aOne (by decide) (by decide), o₃ aOne (by decide),
      o₂ aOne (by decide) (by decide), o₁ aOne (by decide) (by decide), hO]
  -- `c = ⌈q_len / 8⌉` words: `q < 2^(64 c)`.
  have hk1 : 1 ≤ (I.ql + 7) / 8 := by have := L.ql1; omega_using [this]
  have hk : (I.ql + 7) / 8 < wW I.cap := by have := L.qcap; simp only [wW, wk]; omega_using [this]
  refine WP.mono (ckWModOne_ok h₅ L (m₅.trans (m₄.trans m₃)) O₅ (topQ_ok h₅.args.ql
    (by have := L.ql2; have := L.k2; omega_arith) (by have := h₅.ws.h256; omega_using [this])) hk1 hk (ckLenQ_ok (wW I.cap) (by omega_arith) (by rw [eW]; omega_arith))
    (by rw [eW]; omega_arith) (by rw [eW]; omega_arith))
    fun t ⟨ht, ⟨r, hr, mt⟩, ot⟩ => ?_
  have M₅ : I.av s₅.mem aM = I.P := by
    rw [o₅ aM (by decide) (by decide), o₄ aM (by decide) (by decide), o₃ aM (by decide), M₂]
  rw [v₅, M₅] at hr
  have keep : ∀ i, i = 0 ∨ i = aE ∨ i = aOne → I.av t.mem i = I.av s.mem i := by
    intro i hi
    have h16 : i < 16 := by rcases hi with rfl | rfl | rfl <;> decide
    have d1 : i ≠ aM := by rcases hi with rfl | rfl | rfl <;> decide
    have d2 : i ≠ aX := by rcases hi with rfl | rfl | rfl <;> decide
    have d3 : i ≠ aA := by rcases hi with rfl | rfl | rfl <;> decide
    have d4 : i ≠ aRem := by rcases hi with rfl | rfl | rfl <;> decide
    have d5 : i ≠ aT := by rcases hi with rfl | rfl | rfl <;> decide
    have d6 : i ≠ aR := by rcases hi with rfl | rfl | rfl <;> decide
    have d7 : i ≠ CheckCrtKey.aQ := by rcases hi with rfl | rfl | rfl <;> decide
    rw [ot i h16 d4 d7 d5, o₅ i h16 d3, o₄ i h16 d6, o₃ i h16, o₂ i h16 d2, o₁ i h16 d1]
  refine ⟨decide (I.QI < I.P) && decide (r = 1), ⟨ht, ?_, by rw [keep 0 (.inl rfl), hN],
    by rw [keep aE (.inr (.inl rfl)), hE], by rw [keep aOne (.inr (.inr rfl)), hO]⟩, fun hP hpq => ?_⟩
  · rw [mt]
    cases decide (r = 1) <;> cases decide (I.QI < I.P) <;> cases c <;> rfl
  · by_cases hlt : I.QI < I.P
    · have hq : I.Q < 2 ^ (64 * ((I.ql + 7) / 8)) := Nat.lt_of_lt_of_le (os2ip_lt I.qb)
        (by rw [L.qbl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
            exact Nat.pow_le_pow_right (by decide) (by omega_using []))
      rw [hr (Nat.lt_of_le_of_lt (mul_div_top_le hq) hlt) (fun hG => ⟨?_, ?_, ?_⟩), Nat.mul_comm I.QI I.Q]
      · -- `q qInv < q p = n < 2^(64 w)`.
        have hN : I.N < 2 ^ (64 * wk I.k) := lt_w (by rw [L.nl])
        rw [eW, show (2 * wk I.k + 2 - 2) / 2 = wk I.k by omega_arith, Nat.mul_comm I.QI I.Q]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)) (by rw [Nat.mul_comm, hpq]; exact hN)
      · exact Nat.le_trans (hPg hG hpq).1 (Nat.sub_le _ _)
      · exact (hPg hG hpq).2
    · simp only [hlt, decide_false, Bool.false_and]

end VG.Proof.Rsa.AArch64
