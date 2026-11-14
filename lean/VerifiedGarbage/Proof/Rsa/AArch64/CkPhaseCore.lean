module

public import VerifiedGarbage.Proof.Rsa.AArch64.CkState
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Rsa.AArch64.CkSteps`, which only this module used -/

section

/-!
# `vg_rsa_check_key` on AArch64: the pieces on `CkS`

Each piece of `main` keeps `CkS`; what it does to the arrays' values
(`CkIn.av`, over `W` words) and to the mask, and which arrays it leaves.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The value of array `j` over `W` words. -/
abbrev CkIn.av (I : CkIn) (m : Mem) (j : Nat) : Nat := wv m I.B (slot (wW I.cap) j) (wW I.cap)

/-- The mask after a piece that changes only array `j`. -/
theorem mword_arr {m m' : Mem} {B : Addr} {W j L : Nat} (o : Outside B (slot W j) L m m') :
    mword m' B = mword m B :=
  o.word (Or.inl (by have := hdr_lt_slot W j (show Public.sMask < 32 by decide); omega_arith))
    (by simp only [Public.sMask, sFn]; omega_arith)

theorem CkS.av_out {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {m m' : Mem} {j L : Nat}
    (o : Outside I.B (slot (wW I.cap) j) L m m') (hL : L ≤ 8 * (wW I.cap + 2)) {i : Nat} (hi : i < 16) (hij : i ≠ j) :
    I.av m' i = I.av m i :=
  outside_arr o hL hij (by omega_arith) hi h.ws.hZ h.ws.scr.nowrap

/-- `loadA j`: the bytes `bs` into array `j`. -/
theorem ckLoad_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem I.B (8 * sPtr) = p) (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s I.B I.Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlk : len ≤ I.k) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem j = Spec.Rsa.os2ip bs ∧
      ∀ i < 16, i ≠ j → I.av t.mem i = I.av s.mem i :=
  WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hlen hl1 (by have := h.fit; omega_arith)) fun _ ⟨hv, o, _, _, k⟩ =>
    ⟨h.arr hj (Nat.le_refl _) o k (by decide), mword_arr o, hv, fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `ltA a b`: the mask of `[a] < [b]`. -/
theorem ckLt_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (ltA a b)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a < I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i :=
  WP.mono (ltA_ok h.ws ha hb hm) fun _ ⟨hmt, k⟩ =>
    let ⟨ht, hw, hv⟩ := h.mask hmt k (by decide)
    ⟨ht, hw, hv⟩

/-- `eqA a b` and `andZero`: the mask of `[a] = [b]`. -/
theorem ckEq_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {a b : Nat} (ha : a < 16) (hb : b < 16)
    {c : Bool} (hm : mword s.mem I.B = mask c) :
    WP isa (seqs (eqA a b ++ ([.block andZero] : List (Prog isa)))) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mask (decide (I.av s.mem a = I.av s.mem b) && c) ∧
      ∀ i < 16, I.av t.mem i = I.av s.mem i := by
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h.ws ha hb) fun s₁ ⟨hz, m₁, _, _, k₁⟩ => ?_)
  have h₁ : CkS I m₀ s₁ := h.step (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁.ws (by rw [m₁]; exact hm) hz) fun t ⟨⟨hmt, _⟩, k⟩ => ?_
  obtain ⟨ht, hw, hv⟩ := h₁.mask hmt k (by decide)
  exact ⟨ht, hw, fun i hi => by unfold CkIn.av; rw [hv i hi, m₁]⟩

theorem CkLens.w1 {I : CkIn} (L : CkLens I) : 1 ≤ wk I.cap := by have := L.cap1; simp only [wk]; omega_arith

/-- `mulE`: `[aA] := [aX] e`, `e` the low word of `[aE]`. -/
theorem ckMulE_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 2 ^ (64 * wk I.cap)) :
    WP isa (seqs mulE) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      I.av t.mem aA = I.av s.mem aX * (word s.mem I.B (slot (wW I.cap) aE)).toNat ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulE_ok h.ws L.w1 rfl hX) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `mulPQ`: `[aA] := [aX] [aR]`, for `[aX] < 256^p_len` and `[aR] < 256^q_len`. -/
theorem ckMulPQ_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) (L : CkLens I)
    (hX : I.av s.mem aX < 256 ^ I.pl) (hR : I.av s.mem aR < 256 ^ I.ql) :
    WP isa (seqs mulPQ) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aA = I.av s.mem aX * I.av s.mem aR ∧
      ∀ i < 16, i ≠ aA → I.av t.mem i = I.av s.mem i :=
  WP.mono (mulPQ_ok h.ws h.args.pl h.args.ql L.pl1 L.ql1 (by have := L.pcap; simp only [wk]; omega_using [this])
    (by have := L.qcap; simp only [wk]; omega_using [this]) rfl hX rfl hR) fun _ ⟨hv, o, k⟩ =>
    ⟨h.arr (by decide) (Nat.le_refl _) o k (by decide), mword_arr o, hv,
      fun _ hi hij => h.av_out o (Nat.le_refl _) hi hij⟩

/-- `decA aM`: `[aM] - 1`, for an odd `[aM]`. -/
theorem ckDec_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (.block (decA aM)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aM % 2 = 1 → I.av t.mem aM = I.av s.mem aM - 1) ∧
      ∀ i < 16, i ≠ aM → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  refine WP.mono (decA_ok h.ws (j := aM) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s.mem I.B (word s.mem I.B (slot (wW I.cap) aM) - 1) (d := slot (wW I.cap) aM) (by omega_arith)
  rw [← m] at o
  refine ⟨h.arr (by decide) (by omega_arith) o k (by decide), mword_arr o, fun ho => ?_,
    fun _ hi hij => h.av_out o (by omega_arith) hi hij⟩
  have w1 := h.ws.w1
  have e3 := wv_low (m := t.mem) (B := I.B) (e := slot (wW I.cap) aM) (w := wW I.cap) (by omega_arith)
  have e2 := wv_low (m := s.mem) (B := I.B) (e := slot (wW I.cap) aM) (w := wW I.cap) (by omega_arith)
  have hw3 : word t.mem I.B (slot (wW I.cap) aM) = word s.mem I.B (slot (wW I.cap) aM) - 1 := by
    rw [m, word_writeW_self]
  have hup : wv t.mem I.B (slot (wW I.cap) aM + 8) (wW I.cap - 1) = wv s.mem I.B (slot (wW I.cap) aM + 8) (wW I.cap - 1) := by
    rw [m]; exact (writeW_outside s.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith)
  unfold CkIn.av at ho ⊢
  rw [e2] at ho ⊢
  have hodd : (word s.mem I.B (slot (wW I.cap) aM)).toNat % 2 = 1 := by omega_arith
  have hsub : (word s.mem I.B (slot (wW I.cap) aM) - 1).toNat = (word s.mem I.B (slot (wW I.cap) aM)).toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)]; rfl
  rw [e3, hup, hw3, hsub]
  omega_arith

/-- `[aOne] := 1`. -/
theorem ckOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) :
    WP isa (seqs [zeroA aOne, .block (setOneA aOne)]) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧ I.av t.mem aOne = 1 ∧
      ∀ i < 16, i ≠ aOne → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  have sO := h.ws.sl (j := aOne) (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aOne) (by decide)) fun s₁ ⟨hz, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (setOneA_ok h₁.ws (j := aOne) (by decide)) fun t ⟨m, k⟩ => ?_
  have o := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot (wW I.cap) aOne) (by omega_arith)
  rw [← m] at o
  refine ⟨h₁.arr (by decide) (by omega_arith) o k (by decide), (mword_arr o).trans (mword_arr o₁), ?_,
    fun i hi hij => (h₁.av_out o (by omega_arith) hi hij).trans (h.av_out o₁ (Nat.le_refl _) hi hij)⟩
  have w1 := h.ws.w1
  have hz' : ∀ q < wW I.cap + 2, word s₁.mem I.B (slot (wW I.cap) aOne + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  unfold CkIn.av
  rw [wv_low (by omega_arith), m, word_writeW_self, (writeW_outside s₁.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith),
    wv_zero (n := wW I.cap - 1) fun q hq => by rw [Nat.add_assoc, ← Nat.mul_one 8, ← Nat.mul_add]; exact hz' _ (by omega_arith)]
  rfl

end VG.Proof.Rsa.AArch64

end

end


/-!
# Shared RSA key-validation phases on AArch64

`KS c` tracks `CkS`, the accumulated mask, and the arrays holding `n`, `e`
and 1. The full and CRT checkers share the comparison and multiplication
phases and the arithmetic helpers here.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev CkIn.N (I : CkIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CkIn.E (I : CkIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev CkIn.D (I : CkIn) : Nat := Spec.Rsa.os2ip I.db
abbrev CkIn.P (I : CkIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CkIn.Q (I : CkIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CkIn.DP (I : CkIn) : Nat := Spec.Rsa.os2ip I.dpb
abbrev CkIn.DQ (I : CkIn) : Nat := Spec.Rsa.os2ip I.dqb
abbrev CkIn.QI (I : CkIn) : Nat := Spec.Rsa.os2ip I.qib

/-- What `wordGuard` checks: `16 | k`, `p_len = q_len = k / 2` and `n`'s top
bit. -/
def CkIn.Gd (I : CkIn) : Prop :=
  I.k % 16 = 0 ∧ 2 * I.pl = I.k ∧ I.pl = I.ql ∧ ∃ h : 0 < I.nb.length, 128 ≤ (I.nb[0]'h).toNat

/-- A number of `len ≤ k` bytes fits in `w` words. -/
theorem lt_w {bs : List Byte} {k : Nat} (hl : bs.length ≤ k) : Spec.Rsa.os2ip bs < 2 ^ (64 * wk k) :=
  Nat.lt_of_lt_of_le (os2ip_lt bs) (Nat.le_trans (Nat.pow_le_pow_right (by decide) hl)
    (Nat.le_trans (pow256_le_wk k) (Nat.pow_le_pow_right (by decide) (by simp only [wk]; omega_using []))))

/-- Between the phases. -/
def KS (I : CkIn) (m₀ : Mem) (c : Bool) (s : State) : Prop :=
  CkS I m₀ s ∧ mword s.mem I.B = mask c ∧ I.av s.mem 0 = I.N ∧ I.av s.mem aE = I.E ∧ I.av s.mem aOne = 1

/-- `d < n`. -/
theorem phDN_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sD sDlen ++ ltA aX 0)) s (KS I m₀ (decide (I.D < I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.d hs.args.dl hs.d L.dbl L.dl1 L.dl2) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckLt_ok h₁ (a := aX) (b := 0) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  rw [v₁, o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [ot 0 (by decide), o₁ 0 (by decide) (by decide), hN],
    by rw [ot aE (by decide), o₁ aE (by decide) (by decide), hE], by rw [ot aOne (by decide), o₁ aOne (by decide) (by decide), hO]⟩

/-- `p q = n`. -/
theorem phPQ_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulPQ ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) s
      (KS I m₀ (decide (I.P * I.Q = I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [mulPQ]) (WP.mono (ckLoad_ok h₁ (j := aR) (by decide)
    (by decide) (by decide) h₁.args.q h₁.args.ql h₁.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have x₂ : I.av s₂.mem aX = I.P := by rw [o₂ aX (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [mulPQ]) (by simp [eqA]) (WP.mono (ckMulPQ_ok h₂ L
    (by rw [x₂]; have := os2ip_lt I.pb; rw [L.pbl] at this; exact this)
    (by rw [v₂]; have := os2ip_lt I.qb; rw [L.qbl] at this; exact this)) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine WP.mono (ckEq_ok h₃ (a := aA) (b := 0) (by decide) (by decide) (m₃.trans (m₂.trans (m₁.trans hm))))
    fun t ⟨ht, mt, ot⟩ => ?_
  have k0 : ∀ i < 16, i ≠ aX → i ≠ aR → i ≠ aA → I.av t.mem i = I.av s.mem i := fun i hi h1 h2 h3 => by
    rw [ot i hi, o₃ i hi h3, o₂ i hi h2, o₁ i hi h1]
  rw [v₃, x₂, v₂, o₃ 0 (by decide) (by decide), o₂ 0 (by decide) (by decide), o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [k0 0 (by decide) (by decide) (by decide) (by decide), hN],
    by rw [k0 aE (by decide) (by decide) (by decide) (by decide), hE],
    by rw [k0 aOne (by decide) (by decide) (by decide) (by decide), hO]⟩

/-- The low word of `[aE]` is `e`, below `2^64`. -/
theorem e_word {I : CkIn} {m : Mem} (hE : I.av m aE = I.E) (hE64 : I.E < 2 ^ 64) :
    (word m I.B (slot (wW I.cap) aE)).toNat = I.E := by
  rw [← wv_mod64 m I.B (slot (wW I.cap) aE) (n := wW I.cap) (by simp only [wW]; omega_using []), show wv m I.B (slot (wW I.cap) aE) (wW I.cap) = I.E
    from hE, Nat.mod_eq_of_lt hE64]

end VG.Proof.Rsa.AArch64
