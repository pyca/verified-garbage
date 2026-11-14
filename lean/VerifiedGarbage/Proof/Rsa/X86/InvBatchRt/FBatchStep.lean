module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.State
public import VerifiedGarbage.Proof.Divstep.Libsecp
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Batch
import VerifiedGarbage.Proof.Weierstrass.X86.InvMatrix
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Update
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red

/-! # The fused batches on i686: a whole batch

`batchGen_ok`: from the state at byte `i` of the elements to byte `o` (`i, o` being `0, 8` or
`8, 0`), the window's thirty divsteps applied to `f, g` and, with libsecp's `md`, `me`, to `d, e`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx kw_eq MatrixAt bodyWrites)
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Proof.Weierstrass.X86.Inv (wordState atWord)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-! ## The window, and `md`, `me` -/

/-- The window's thirty word divsteps from `f`, `g`'s low words. -/
theorem windowF_ok {s : State} {n : Nat} (h : Bx L s B Z len N n) {i : Nat} (hi : i + 8 ≤ fgSz) {d f g : Int}
    (hd : s.mem.readW (off B win) 32 = BitVec.ofInt 32 d)
    (hf : ((s.mem.readW (off B (fg0 len + i)) 32).toNat : Int) % 2 ^ 32 = f % 2 ^ 32)
    (hg : ((s.mem.readW (off B (fg0 len + (i + 4))) 32).toNat : Int) % 2 ^ 32 = g % 2 ^ 32)
    (hdb : |d| + 64 < 2 ^ 30) (hfo : f % 2 = 1) :
    WP isa (.seq (.block (startF L i)) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)) s fun z =>
      Bx L z B Z len N n ∧ MatrixAt B (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside B win 28 s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have e16 : win = 16 := rfl
  have e96 : halfSlot = 96 := rfl
  refine WP.seq (WP.mono (startF_ok h hi) fun s₁ ⟨H₁, V₁, K₁, O₁⟩ => ?_)
  have rel : (wordState s₁.mem B win).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd, rfl, rfl, rfl, rfl, hf, hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.wordSteps_ok H₁.ws.ws.workspace (t := win) (by omega_using [hZ, e16, e96])
    (by decide) (by decide)) fun z ⟨V₂, K₂, O₂⟩ => ⟨H₁.keepLow K₂ (by decide) (by decide) O₂ (by decide), ?_,
      (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega_using [hx])]

theorem toInt_of_cong (x : BitVec 32) {z : Int} (h : (x.toNat : Int) ≡ z [ZMOD 2 ^ 32]) (h1 : -2 ^ 31 ≤ z)
    (h2 : z < 2 ^ 31) : x.toInt = z := by
  have := x.isLt
  unfold Int.ModEq at h
  rw [toInt_cond x]
  split <;> omega_arith

theorem toNat_cong (x : BitVec 32) : (x.toNat : Int) ≡ x.toInt [ZMOD 2 ^ 32] := by
  have := x.isLt
  unfold Int.ModEq; rw [toInt_cond x]; split <;> omega_using []

theorem toNat_add_cong (x y : BitVec 32) : ((x + y).toNat : Int) ≡ x.toNat + y.toNat [ZMOD 2 ^ 32] := by
  rw [BitVec.toNat_add]; push_cast; exact Int.mod_modEq _ _

theorem toNat_mul_cong (x y : BitVec 32) : ((x * y).toNat : Int) ≡ x.toNat * y.toNat [ZMOD 2 ^ 32] := by
  rw [BitVec.toNat_mul]; push_cast; exact Int.mod_modEq _ _

theorem toNat_sub_cong (x y : BitVec 32) : ((x - y).toNat : Int) ≡ x.toNat - y.toNat [ZMOD 2 ^ 32] := by
  have := y.isLt
  rw [BitVec.toNat_sub]; unfold Int.ModEq; push_cast [Nat.cast_sub (le_of_lt this)]; omega_using []

theorem and_sel_cong (x : BitVec 32) (c : Prop) [Decidable c] :
    ((x &&& (if c then -1 else 0)).toNat : Int) ≡ (if c then x.toInt else 0) [ZMOD 2 ^ 32] := by
  split
  · rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]; exact toNat_cong x
  · simp

/-- `mdme`'s word is `mdOf`'s `md`, for `d`, `e` with those low words and signs. -/
theorem mdWord_spec {U V SD SE D0 E0 NP : BitVec 32} {d e np : Int}
    (huv : |U.toInt| + |V.toInt| ≤ 2 ^ 30)
    (hsd : SD = if d < 0 then -1 else 0) (hse : SE = if e < 0 then -1 else 0)
    (hd : (D0.toNat : Int) ≡ d [ZMOD 2 ^ 32]) (he : (E0.toNat : Int) ≡ e [ZMOD 2 ^ 32])
    (hnp : (NP.toNat : Int) ≡ np [ZMOD 2 ^ 32]) :
    (mdWord U V SD SE D0 E0 NP).toInt = Divstep.mdOf 30 np U.toInt V.toInt d e := by
  set u := U.toInt; set v := V.toInt
  have cu := toNat_cong U; have cv := toNat_cong V
  set md0 := (if d < 0 then u else 0) + (if e < 0 then v else 0)
  have c0 : (((U &&& SD) + (V &&& SE)).toNat : Int) ≡ md0 [ZMOD 2 ^ 32] := by
    rw [hsd, hse]
    exact (toNat_add_cong _ _).trans ((and_sel_cong U _).add (and_sel_cong V _))
  have cX : ((NP * (U * D0 + V * E0)).toNat : Int) ≡ np * (u * d + v * e) [ZMOD 2 ^ 32] :=
    (toNat_mul_cong _ _).trans (hnp.mul ((toNat_add_cong _ _).trans
      (((toNat_mul_cong _ _).trans (cu.mul hd)).add ((toNat_mul_cong _ _).trans (cv.mul he)))))
  have cY := (toNat_sub_cong ((U &&& SD) + (V &&& SE)) (NP * (U * D0 + V * E0))).trans (c0.sub cX)
  -- The low 30 bits.
  set Y := (U &&& SD) + (V &&& SE) - NP * (U * D0 + V * E0)
  have hz : ((Y &&& 0x3FFFFFFF#32).toNat : Int) = (md0 - np * (u * d + v * e)) % 2 ^ 30 := by
    have h1 : (Y &&& 0x3FFFFFFF#32).toNat = Y.toNat % 2 ^ 30 := by
      rw [BitVec.toNat_and, show (0x3FFFFFFF#32).toNat = 2 ^ 30 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rw [h1]; push_cast
    have := Int.ModEq.of_dvd (show (2 : Int) ^ 30 ∣ 2 ^ 32 by decide) cY
    exact this
  have cR : ((mdWord U V SD SE D0 E0 NP).toNat : Int) ≡ Divstep.mdOf 30 np u v d e [ZMOD 2 ^ 32] := by
    unfold mdWord Divstep.mdOf
    refine (toNat_sub_cong _ _).trans (c0.sub ?_)
    rw [hz]
  obtain ⟨b1, b2⟩ := Divstep.mdOf_abs (N := 30) (np := np) (u := u) (v := v) (d := d) (e := e) huv
  simp only [Nat.reduceAdd] at b1
  exact toInt_of_cong _ cR (by omega_using [b1]) (by omega_using [b2])

/-- A batch's matrix and new state. -/
def bT (dl f g : Int) : Divstep.MSt := Divstep.msteps 30 (Divstep.MSt.init dl f g)
def fNext (dl f g : Int) : Int := ((bT dl f g).u * f + (bT dl f g).v * g) / 2 ^ 30
def gNext (dl f g : Int) : Int := ((bT dl f g).q * f + (bT dl f g).r * g) / 2 ^ 30
def dNext (p iv : Nat) (dl f g d e : Int) : Int := Divstep.deUpd 30 p iv (bT dl f g).u (bT dl f g).v d e
def eNext (p iv : Nat) (dl f g d e : Int) : Int := Divstep.deUpd 30 p iv (bT dl f g).q (bT dl f g).r d e

/-- What a batch writes: the header to the counter, the scratch words after the header, and the
interleaved arrays. -/
def batchWrites (len : Nat) : List (Nat × Nat) :=
  [(win, 88), (160, 48), (rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 4), 3 * (8 * nw len + 8)),
    (rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 11), 4 * (8 * nw len + 8))]

/-- The bounds a batch's results need. -/
def InRange (n : Nat) (x : Int) : Prop := -(2 ^ (32 * n) * 2 ^ 31) ≤ x ∧ x < 2 ^ (32 * n) * 2 ^ 31

theorem batchGen_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) (he : nw len % 2 = 0) {i o : Nat}
    (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) {p iv : Nat} {dl f g d e : Int}
    (F : FAt len B p iv dl f g d e i s) (hdl : |dl| + 64 < 2 ^ 30) (hfo : f % 2 = 1)
    (hf' : InRange (nw len) (fNext dl f g)) (hg' : InRange (nw len) (gNext dl f g))
    (hd' : InRange (nw len) (dNext p iv dl f g d e)) (he' : InRange (nw len) (eNext p iv dl f g d e)) :
    WP isa (batchCodeF L i o) s fun t =>
      Bx L t B Z len N ∧ Keeps wordClob s t ∧ Unch B (batchWrites len) s.mem t.mem ∧
      VG.Proof.Mont.w32 t.mem B 100 = VG.Proof.Mont.w32 s.mem B 100 ∧
      FAt len B p iv (bT dl f g).d (fNext dl f g) (gNext dl f g) (dNext p iv dl f g d e) (eNext p iv dl f g d e) o t := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have ke := kw_eq len
  have e16 : win = 16 := rfl; have eMu : sMu = 160 := rfl; have eP : sP = 176 := rfl
  have eMd : sMd = 184 := rfl; have eMm : sMm = 200 := rfl
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  have hAF : rv (kw len) { arr := fgArr } = 160 + 4 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, fgArr]; omega_using []
  have hAD : rv (kw len) { arr := deArr } = 160 + 11 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, deArr]; omega_using []
  have hfg0 : fg0 len = rv (kw len) { arr := fgArr } + fgSz := by simp only [fg0, rv]; omega_using []
  have hde0 : de0 len = rv (kw len) { arr := deArr } + deSz := by simp only [de0, rv]; omega_using []
  have Fdl := F.dl; have Fiv := F.inverse; have Ff := F.f; have Fg := F.g; have Fd := F.d; have Fe := F.e
  have Fp := F.p
  have hi8 : i ≤ 8 := by omega_using [hio]
  have hoi : (i + 4 ≤ o ∨ o + 4 ≤ i) ∧ (i + 4 + 4 ≤ o ∨ o + 4 ≤ i + 4) ∧ (i + 4 ≤ o + 4 ∨ o + 4 + 4 ≤ i) ∧
      (i + 4 + 4 ≤ o + 4 ∨ o + 4 + 4 ≤ i + 4) := by omega_using [hio]
  generalize hA : rv (kw len) { arr := fgArr } = AF at hAF hfg0 Ff Fg
  generalize hD : rv (kw len) { arr := deArr } = AD at hAD hde0 Fd Fe Fp
  set T := bT dl f g with hT
  have bnd := Divstep.msteps_bnd dl f g 30
  simp only [Divstep.MSt.bnd] at bnd
  unfold batchCodeF
  simp only [seqs]
  -- The window.
  have hfw : ((s.mem.readW (off B (fg0 len + i)) 32).toNat : Int) % 2 ^ 32 = f % 2 ^ 32 := by
    have := sval_low s.mem B (AF + fgSz + i) fgSz (nw len)
    rw [Ff] at this; rw [hfg0]; exact this
  have hgw : ((s.mem.readW (off B (fg0 len + (i + 4))) 32).toNat : Int) % 2 ^ 32 = g % 2 ^ 32 := by
    have := sval_low s.mem B (AF + fgSz + (i + 4)) fgSz (nw len)
    rw [Fg] at this; rw [hfg0]; exact this
  refine VG.Proof.Rsa.X86.InvBatchRt.seq_assoc (WP.seq (WP.mono (windowF_ok h (by omega_using [hio, efs]) F.dl hfw hgw hdl hfo)
    fun s₁ ⟨H₁, M₁, K₁, O₁⟩ => ?_))
  have hn20 : AF + fgSz * (nw len + 2) < Z := by rw [efs]; omega_using [hf16, ke, hAF]
  have hd20 : AD + deSz * (nw len + 2) < Z := by rw [eds]; omega_using [hn2, hf16, ke, hAD]
  have far : AF + fgSz * (nw len + 2) ≤ AD := by rw [efs]; omega_using [ke, hAF, hAD]
  -- The masks.
  refine WP.seq (WP.mono (coefMasks_ok H₁) fun s₂ ⟨H₂, V₂, O₂, K₂⟩ => ?_)
  have c₂ : ∀ d, d + 4 ≤ win + 28 → win + 12 ≤ d →
      s₂.mem.readW (off B d) 32 = s₁.mem.readW (off B d) 32 := fun d h1 h2 => hdr_out O₂ (.inl (by omega_using [e16, eMu, h1])) (by omega_using [e16, h1])
  have Sf₂ : Same B (AF + fgSz + i) fgSz (nw len + 1) s.mem s₂.mem :=
    (Same.below O₁ (by omega_using [hio, efs]) (by omega_using [e16, hAF]) (by omega_using [hn, hn20])).trans (Same.below O₂ (by omega_using [hio, efs]) (by omega_using [eMu, hAF]) (by omega_using [hn, hn20]))
  have Sg₂ : Same B (AF + fgSz + (i + 4)) fgSz (nw len + 1) s.mem s₂.mem :=
    (Same.below O₁ (by omega_using [hio, efs]) (by omega_using [e16, hAF]) (by omega_using [hn, hn20])).trans (Same.below O₂ (by omega_using [hio, efs]) (by omega_using [eMu, hAF]) (by omega_using [hn, hn20]))
  have mk₂ : ∀ j < 4, s₂.mem.readW (off B (sMu + 4 * j)) 32 = maskW (s₂.mem.readW (off B (win + 12 + 4 * j)) 32) :=
    fun j hj => by rw [V₂ j hj, c₂ _ (by omega_using [hj]) (by omega_using [])]
  have hu₂ : s₂.mem.readW (off B (win + 12)) 32 = BitVec.ofInt 32 T.u := by rw [c₂ _ (by omega_using []) (by omega_using [])]; exact M₁.u
  have hv₂ : s₂.mem.readW (off B (win + 16)) 32 = BitVec.ofInt 32 T.v := by rw [c₂ _ (by omega_using []) (by omega_using [])]; exact M₁.v
  have hq₂ : s₂.mem.readW (off B (win + 20)) 32 = BitVec.ofInt 32 T.q := by rw [c₂ _ (by omega_using []) (by omega_using [])]; exact M₁.q
  have hr₂ : s₂.mem.readW (off B (win + 24)) 32 = BitVec.ofInt 32 T.r := by rw [c₂ _ (by omega_using []) (by omega_using [])]; exact M₁.r
  -- The row of `f`.
  have tsF : ∀ {m : Mem} {c₁ c₂ m₁ m₂ : Nat} (o' : Nat), o' + 4 ≤ fgSz → (i + 4 ≤ o' ∨ o' + 4 ≤ i) →
      (i + 4 + 4 ≤ o' ∨ o' + 4 ≤ i + 4) → c₁ + 4 ≤ sP → c₂ + 4 ≤ sP → m₁ + 4 ≤ sP → m₂ + 4 ≤ sP →
      m.readW (off B m₁) 32 = maskW (m.readW (off B c₁) 32) → m.readW (off B m₂) 32 = maskW (m.readW (off B c₂) 32) →
      TermsOk m B AF fgSz o' [⟨i, c₁, m₁⟩, ⟨i + 4, c₂, m₂⟩] := by
    intro m c₁ c₂ m₁ m₂ o' h1 h2 h3 h4 h5 h6 h7 h8 h9 t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨show c₁ + 4 ≤ AF by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, h1, h4, h5, h6, h7], show m₁ + 4 ≤ AF by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, h1, h4, h5, h6, h7], show i + 4 ≤ fgSz by rw [efs]; omega_using [hio],
        h2, .inl h4, .inl h6, h8⟩
    · exact ⟨show c₂ + 4 ≤ AF by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, h1, h4, h5, h6, h7], show m₂ + 4 ≤ AF by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, h1, h4, h5, h6, h7], show i + 4 + 4 ≤ fgSz by rw [efs]; omega_using [hio],
        h3, .inl h5, .inl h7, h9⟩
  have huv : |T.u| + |T.v| ≤ 2 ^ 30 := bnd.1
  have hqr : |T.q| + |T.r| ≤ 2 ^ 30 := bnd.2
  have ts₂ : TermsOk s₂.mem B AF fgSz o [⟨i, win + 12, sMu⟩, ⟨i + 4, win + 16, sMu + 4⟩] := by
    refine tsF o (by rw [efs]; omega_using [hio]) hoi.1 hoi.2.1 (by omega_using [e16, eP]) (by omega_using [e16, eP]) (by omega_using [eMu, eP]) (by omega_using [eMu, eP]) ?_ ?_
    · simpa using mk₂ 0 (by omega_using [])
    · simpa using mk₂ 1 (by omega_using [])
  have rf := rowTwo_ok H₂ hn2 he (arr := fgArr) (sz := fgSz) (o := o) (t₁ := ⟨i, win + 12, sMu⟩)
    (t₂ := ⟨i + 4, win + 16, sMu + 4⟩) (Or.inl rfl) (by rw [efs]; omega_using [hio]) (by rw [hA]; omega) (by rw [hA]; omega_using [eP, hAF])
    (by rw [hA]; exact ts₂) hu₂ hv₂ huv
    (by dsimp only; rw [hA, Sf₂.sval_eq, Sg₂.sval_eq, Ff, Fg]; exact hf')
  refine WP.seq (WP.mono rf fun s₃ ⟨H₃, K₃, F₃, V₃⟩ => ?_)
  rw [hA] at F₃ V₃
  dsimp only at V₃
  rw [Sf₂.sval_eq, Sg₂.sval_eq, Ff, Fg] at V₃
  have hAF32 : AF ≤ 2 ^ 32 := by omega_using [hn, hf16, ke, hAF]
  have hfit32 : AF + fgSz * (nw len + 2) ≤ 2 ^ 32 := by rw [efs] at *; omega_using [hn, hf16, ke, hAF]
  have hdit32 : AD + deSz * (nw len + 2) ≤ 2 ^ 32 := by rw [eds] at *; omega_using [hn2, he, hn, hf16, ke, efs, hAF, hAD, hn20, hd20, far, hAF32, hfit32]
  -- The row of `g`.
  have Sf₃ : Same B (AF + fgSz + i) fgSz (nw len + 1) s.mem s₃.mem :=
    Sf₂.trans (Same.row_slot F₃ (by rw [efs]; omega_using [hio]) (by rw [efs]; omega_using [hio]) hoi.1 (by omega_using [eP, hAF]) hfit32)
  have Sg₃ : Same B (AF + fgSz + (i + 4)) fgSz (nw len + 1) s.mem s₃.mem :=
    Sg₂.trans (Same.row_slot F₃ (by rw [efs]; omega_using [hio]) (by rw [efs]; omega_using [hio]) hoi.2.1 (by omega_using [eP, hAF]) hfit32)
  have h₃ : ∀ d, d + 4 ≤ sP → s₃.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd =>
    hdr_row F₃ (by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hd]) (.inl hd) hAF32
  have ts₃ : TermsOk s₃.mem B AF fgSz (o + 4) [⟨i, win + 20, sMu + 8⟩, ⟨i + 4, win + 24, sMu + 12⟩] := by
    refine tsF (o + 4) (by rw [efs]; omega_using [hio]) hoi.2.2.1 hoi.2.2.2 (by omega_using [e16, eP]) (by omega_using [e16, eP]) (by omega_using [eMu, eP]) (by omega_using [eMu, eP]) ?_ ?_
    · rw [h₃ (sMu + 8) (by omega_using [eMu, eP]), h₃ (win + 20) (by omega_using [e16, eP])]; simpa using mk₂ 2 (by omega_using [])
    · rw [h₃ (sMu + 12) (by omega_using [eMu, eP]), h₃ (win + 24) (by omega_using [e16, eP])]; simpa using mk₂ 3 (by omega_using [])
  have rg := rowTwo_ok H₃ hn2 he (arr := fgArr) (sz := fgSz) (o := o + 4) (t₁ := ⟨i, win + 20, sMu + 8⟩)
    (t₂ := ⟨i + 4, win + 24, sMu + 12⟩) (Or.inl rfl) (by rw [efs]; omega_using [hio]) (by rw [hA]; omega) (by rw [hA]; omega_using [eP, hAF])
    (by rw [hA]; exact ts₃) (by rw [h₃ (win + 20) (by omega_using [e16, eP])]; exact hq₂) (by rw [h₃ (win + 24) (by omega_using [e16, eP])]; exact hr₂) hqr
    (by dsimp only; rw [hA, Sf₃.sval_eq, Sg₃.sval_eq, Ff, Fg]; exact hg')
  refine WP.seq (WP.mono rg fun s₄ ⟨H₄, K₄, F₄, V₄⟩ => ?_)
  rw [hA] at F₄ V₄
  dsimp only at V₄
  rw [Sf₃.sval_eq, Sg₃.sval_eq, Ff, Fg] at V₄
  have h₄ : ∀ d, d + 4 ≤ sP → s₄.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd => by
    rw [hdr_row F₄ (by omega_using [hn2, he, hn, hf16, ke, eP, efs, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hd]) (.inl hd) hAF32, h₃ d hd]
  -- `d`, `e`, `p` so far.
  have farDE : ∀ x, x + 4 ≤ deSz → Same B (AD + deSz + x) deSz (nw len + 1) s.mem s₄.mem := fun x hx =>
    (((Same.below O₁ hx (by omega_using [e16, hAD]) hdit32).trans (Same.below O₂ hx (by omega_using [eMu, hAD]) hdit32)).trans
      (Same.row_far F₃ (by rw [efs]; omega_using [hio]) hx (.inr far) (by omega_using [eP, hAD]) hdit32)).trans
      (Same.row_far F₄ (by rw [efs]; omega_using [hio]) hx (.inr far) (by omega_using [eP, hAD]) hdit32)
  have Sd₄ := farDE i (by rw [eds]; omega_using [hio])
  have Se₄ := farDE (i + 4) (by rw [eds]; omega_using [hio])
  have Sp₄ := farDE 16 (by rw [eds])
  -- `md`, `me`.
  refine WP.seq (WP.mono (mdme_ok H₄ (dx := i) (by rw [eds]; omega_using [hio])) fun s₅ ⟨H₅, O₅, K₅, M₅⟩ => ?_)
  have iv₄ : (s₄.mem.readW (off B (win + 28)) 32).toNat = iv := by
    rw [h₄ (win + 28) (by omega_using [e16, eP]), hdr_out O₂ (.inl (by omega_using [e16, eMu])) (by omega_using [e16]), ← Fiv]
    exact O₁.w32 (.inr (by omega_using [])) (by omega_using [e16])
  have sd : maskW (s₄.mem.readW (off B (de0 len + 20 * nw len + i)) 32) = if d < 0 then -1 else 0 := by
    rw [show de0 len + 20 * nw len + i = AD + deSz + i + deSz * nw len by rw [hde0, eds]; omega_using [], maskW_top,
      Sd₄.sval_eq, Fd]
  have se : maskW (s₄.mem.readW (off B (de0 len + 20 * nw len + (i + 4))) 32) = if e < 0 then -1 else 0 := by
    rw [show de0 len + 20 * nw len + (i + 4) = AD + deSz + (i + 4) + deSz * nw len by rw [hde0, eds]; omega_using [],
      maskW_top, Se₄.sval_eq, Fe]
  have d0 : ((s₄.mem.readW (off B (de0 len + i)) 32).toNat : Int) ≡ d [ZMOD 2 ^ 32] := by
    have := sval_low s₄.mem B (AD + deSz + i) deSz (nw len)
    rw [Sd₄.sval_eq, Fd] at this; rw [hde0]; exact this
  have e0 : ((s₄.mem.readW (off B (de0 len + (i + 4))) 32).toNat : Int) ≡ e [ZMOD 2 ^ 32] := by
    have := sval_low s₄.mem B (AD + deSz + (i + 4)) deSz (nw len)
    rw [Se₄.sval_eq, Fe] at this; rw [hde0]; exact this
  have np : ((s₄.mem.readW (off B (win + 28)) 32).toNat : Int) ≡ (iv : Int) [ZMOD 2 ^ 32] := by rw [iv₄]
  have hu₄ : s₄.mem.readW (off B (win + 12)) 32 = BitVec.ofInt 32 T.u := by rw [h₄ (win + 12) (by omega_using [e16, eP])]; exact hu₂
  have hv₄ : s₄.mem.readW (off B (win + 16)) 32 = BitVec.ofInt 32 T.v := by rw [h₄ (win + 16) (by omega_using [e16, eP])]; exact hv₂
  have hq₄ : s₄.mem.readW (off B (win + 20)) 32 = BitVec.ofInt 32 T.q := by rw [h₄ (win + 20) (by omega_using [e16, eP])]; exact hq₂
  have hr₄ : s₄.mem.readW (off B (win + 24)) 32 = BitVec.ofInt 32 T.r := by rw [h₄ (win + 24) (by omega_using [e16, eP])]; exact hr₂
  have tu : (BitVec.ofInt 32 T.u).toInt = T.u := ofInt_toInt (by have := abs_nonneg T.v; omega_using [huv, this])
  have tv : (BitVec.ofInt 32 T.v).toInt = T.v := ofInt_toInt (by have := abs_nonneg T.u; omega_using [huv, this])
  have tq : (BitVec.ofInt 32 T.q).toInt = T.q := ofInt_toInt (by have := abs_nonneg T.r; omega_using [hqr, this])
  have tr : (BitVec.ofInt 32 T.r).toInt = T.r := ofInt_toInt (by have := abs_nonneg T.q; omega_using [hqr, this])
  have md : (s₅.mem.readW (off B (sMd + 8)) 32).toInt = Divstep.mdOf 30 iv T.u T.v d e := by
    rw [M₅.md, hu₄, hv₄, mdWord_spec (by rw [tu, tv]; exact huv) sd se d0 e0 np, tu, tv]
  have me : (s₅.mem.readW (off B (sMd + 12)) 32).toInt = Divstep.mdOf 30 iv T.q T.r d e := by
    rw [M₅.me, hq₄, hr₄, mdWord_spec (by rw [tq, tr]; exact hqr) sd se d0 e0 np, tq, tr]
  have mdb := Divstep.mdOf_abs (N := 30) (np := (iv : Int)) (d := d) (e := e) huv
  have meb := Divstep.mdOf_abs (N := 30) (np := (iv : Int)) (d := d) (e := e) hqr
  simp only [Nat.reduceAdd] at mdb meb
  have hAD32 : AD ≤ 2 ^ 32 := by omega_using [hdit32]
  -- The row of `d`.
  have h₅ : ∀ d, d + 4 ≤ sP → s₅.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd => by
    rw [hdr_out O₅ (.inl (by omega_using [eP, eMd, hd])) (by omega_using [eP, hd]), h₄ d hd]
  have Sd₅ := Sd₄.trans (Same.below O₅ (by rw [eds]; omega_using [hio]) (by omega_using [eMd, hAD]) hdit32)
  have Se₅ := Se₄.trans (Same.below O₅ (by rw [eds]; omega_using [hio]) (by omega_using [eMd, hAD]) hdit32)
  have Sp₅ := Sp₄.trans (Same.below O₅ (by rw [eds]) (by omega_using [eMd, hAD]) hdit32)
  have tsD : ∀ {m : Mem} {c₁ c₂ c₃ m₁ m₂ m₃ : Nat} (o' : Nat), o' + 4 ≤ deSz → (i + 4 ≤ o' ∨ o' + 4 ≤ i) →
      (i + 4 + 4 ≤ o' ∨ o' + 4 ≤ i + 4) → o' + 4 ≤ 16 → c₁ + 4 ≤ sP → c₂ + 4 ≤ sP → m₁ + 4 ≤ sP → m₂ + 4 ≤ sP →
      sP + 8 ≤ c₃ → sP + 8 ≤ m₃ → c₃ + 4 ≤ AD → m₃ + 4 ≤ AD →
      m.readW (off B m₁) 32 = maskW (m.readW (off B c₁) 32) → m.readW (off B m₂) 32 = maskW (m.readW (off B c₂) 32) →
      m.readW (off B m₃) 32 = maskW (m.readW (off B c₃) 32) →
      TermsOk m B AD deSz o' [⟨i, c₁, m₁⟩, ⟨i + 4, c₂, m₂⟩, ⟨16, c₃, m₃⟩] := by
    intro m c₁ c₂ c₃ m₁ m₂ m₃ o' h1 h2 h3 h3' h4 h5 h6 h7 h8 h9 h10 h11 k1 k2 k3 t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨show c₁ + 4 ≤ AD by omega_using [hn2, he, hn, hf16, ke, eP, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, h1, h4, h5, h6, h7, h8, h9, h10, h11], show m₁ + 4 ≤ AD by omega_using [hn2, he, hn, hf16, ke, eP, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, h1, h4, h5, h6, h7, h8, h9, h10, h11], show i + 4 ≤ deSz by rw [eds]; omega_using [hio],
        h2, .inl h4, .inl h6, k1⟩
    · exact ⟨show c₂ + 4 ≤ AD by omega_using [hn2, he, hn, hf16, ke, eP, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, h1, h4, h5, h6, h7, h8, h9, h10, h11], show m₂ + 4 ≤ AD by omega_using [hn2, he, hn, hf16, ke, eP, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, h1, h4, h5, h6, h7, h8, h9, h10, h11], show i + 4 + 4 ≤ deSz by rw [eds]; omega_using [hio],
        h3, .inl h5, .inl h7, k2⟩
    · exact ⟨show c₃ + 4 ≤ AD by omega_using [h10], show m₃ + 4 ≤ AD by omega_using [h11], show 16 + 4 ≤ deSz by rw [eds],
        .inr h3', .inr h8, .inr h9, k3⟩
  have mk₅ : ∀ j < 4, s₅.mem.readW (off B (sMu + 4 * j)) 32 = maskW (s₅.mem.readW (off B (win + 12 + 4 * j)) 32) :=
    fun j hj => by rw [h₅ (sMu + 4 * j) (by omega_using [eMu, eP, hj]), h₅ (win + 12 + 4 * j) (by omega_using [e16, eP, hj])]; exact mk₂ j hj
  have ts₅ : TermsOk s₅.mem B AD deSz o [⟨i, win + 12, sMu⟩, ⟨i + 4, win + 16, sMu + 4⟩, ⟨16, sMd + 8, sMm⟩] := by
    refine tsD o (by rw [eds]; omega_using [hio]) hoi.1 hoi.2.1 (by omega_using [hio]) (by omega_using [e16, eP]) (by omega_using [e16, eP]) (by omega_using [eMu, eP]) (by omega_using [eMu, eP])
      (by omega_using [eP, eMd]) (by omega_using [eP, eMm]) (by omega_using [eMd, hAD]) (by omega_using [eMm, hAD]) ?_ ?_ M₅.mmd
    · simpa using mk₅ 0 (by omega_using [])
    · simpa using mk₅ 1 (by omega_using [])
  have rd := rowThree_ok H₅ hn2 he (arr := deArr) (sz := deSz) (o := o) (t₁ := ⟨i, win + 12, sMu⟩)
    (t₂ := ⟨i + 4, win + 16, sMu + 4⟩) (t₃ := ⟨16, sMd + 8, sMm⟩) (Or.inr rfl) (by rw [eds]; omega_using [hio])
    (by rw [hD]; omega) (by rw [hD]; omega_using [eP, hAD]) (by rw [hD]; exact ts₅) (by rw [h₅ (win + 12) (by omega_using [e16, eP])]; exact hu₂)
    (by rw [h₅ (win + 16) (by omega_using [e16, eP])]; exact hv₂) md huv (by rw [abs_le]; omega_using [mdb])
    (by dsimp only; rw [hD, Sd₅.sval_eq, Se₅.sval_eq, Sp₅.sv, Fd, Fe, Fp]; exact hd')
  refine WP.seq (WP.mono rd fun s₆ ⟨H₆, K₆, F₆, V₆⟩ => ?_)
  rw [hD] at F₆ V₆
  dsimp only at V₆
  rw [Sd₅.sval_eq, Se₅.sval_eq, Sp₅.sv, Fd, Fe, Fp] at V₆
  -- The row of `e`.
  have h₆ : ∀ d, d + 4 ≤ sP → s₆.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd => by
    rw [hdr_row F₆ (by omega_using [hn2, he, hn, hf16, ke, eP, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, hd]) (.inl hd) hAD32, h₅ d hd]
  have h₆' : ∀ d, sP + 8 ≤ d → d + 4 ≤ AD → s₆.mem.readW (off B d) 32 = s₅.mem.readW (off B d) 32 := fun d h1 h2 =>
    hdr_row F₆ h2 (.inr h1) hAD32
  have Sd₆ := Sd₅.trans (Same.row_slot F₆ (by rw [eds]; omega_using [hio]) (by rw [eds]; omega_using [hio]) hoi.1 (by omega_using [eP, hAD]) hdit32)
  have Se₆ := Se₅.trans (Same.row_slot F₆ (by rw [eds]; omega_using [hio]) (by rw [eds]; omega_using [hio]) hoi.2.1 (by omega_using [eP, hAD]) hdit32)
  have Sp₆ := Sp₅.trans (Same.row_slot F₆ (by rw [eds]; omega_using [hio]) (by rw [eds]) (.inr (by omega_using [hio])) (by omega_using [eP, hAD]) hdit32)
  have ts₆ : TermsOk s₆.mem B AD deSz (o + 4)
      [⟨i, win + 20, sMu + 8⟩, ⟨i + 4, win + 24, sMu + 12⟩, ⟨16, sMd + 12, sMm + 4⟩] := by
    refine tsD (o + 4) (by rw [eds]; omega_using [hio]) hoi.2.2.1 hoi.2.2.2 (by omega_using [hio]) (by omega_using [e16, eP]) (by omega_using [e16, eP]) (by omega_using [eMu, eP])
      (by omega_using [eMu, eP]) (by omega_using [eP, eMd]) (by omega_using [eP, eMm]) (by omega_using [eMd, hAD]) (by omega_using [eMm, hAD]) ?_ ?_ ?_
    · rw [h₆ (sMu + 8) (by omega_using [eMu, eP]), h₆ (win + 20) (by omega_using [e16, eP])]; simpa using mk₂ 2 (by omega_using [])
    · rw [h₆ (sMu + 12) (by omega_using [eMu, eP]), h₆ (win + 24) (by omega_using [e16, eP])]; simpa using mk₂ 3 (by omega_using [])
    · rw [h₆' (sMm + 4) (by omega_using [eP, eMm]) (by omega_using [eMm, hAD]), h₆' (sMd + 12) (by omega_using [eP, eMd]) (by omega_using [eMd, hAD])]; exact M₅.mme
  have me₆ : (s₆.mem.readW (off B (sMd + 12)) 32).toInt = Divstep.mdOf 30 iv T.q T.r d e := by
    rw [h₆' (sMd + 12) (by omega_using [eP, eMd]) (by omega_using [eMd, hAD])]; exact me
  have re := rowThree_ok H₆ hn2 he (arr := deArr) (sz := deSz) (o := o + 4) (t₁ := ⟨i, win + 20, sMu + 8⟩)
    (t₂ := ⟨i + 4, win + 24, sMu + 12⟩) (t₃ := ⟨16, sMd + 12, sMm + 4⟩) (Or.inr rfl) (by rw [eds]; omega_using [hio])
    (by rw [hD]; omega) (by rw [hD]; omega_using [eP, hAD]) (by rw [hD]; exact ts₆) (by rw [h₆ (win + 20) (by omega_using [e16, eP])]; exact hq₂)
    (by rw [h₆ (win + 24) (by omega_using [e16, eP])]; exact hr₂) me₆ hqr
    (by rw [abs_le]; omega_using [meb])
    (by dsimp only; rw [hD, Sd₆.sval_eq, Se₆.sval_eq, Sp₆.sv, Fd, Fe, Fp]; exact he')
  refine WP.mono re fun t ⟨H₇, K₇, F₇, V₇⟩ => ?_
  rw [hD] at F₇ V₇
  dsimp only at V₇
  rw [Sd₆.sval_eq, Se₆.sval_eq, Sp₆.sv, Fd, Fe, Fp] at V₇
  -- The header below the scratch words, from the window on.
  have hT : ∀ d, d + 4 ≤ sMu → t.mem.readW (off B d) 32 = s₁.mem.readW (off B d) 32 := fun d hd => by
    rw [hdr_row F₇ (by omega_using [hn2, he, hn, hf16, ke, eMu, efs, eds, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32, hd]) (.inl (by omega_using [eMu, eP, hd])) hAD32, h₆ d (by omega_using [eMu, eP, hd]), hdr_out O₂ (.inl hd) (by omega_using [eMu, hd])]
  have ST : ∀ {b sz K : Nat}, Same B b sz K s₃.mem s₄.mem → Same B b sz K s₄.mem s₅.mem →
      Same B b sz K s₅.mem s₆.mem → Same B b sz K s₆.mem t.mem → Same B b sz K s₃.mem t.mem :=
    fun a b c d => ((a.trans b).trans c).trans d
  have Sf₇ : Same B (AF + fgSz + o) fgSz (nw len + 1) s₃.mem t.mem :=
    ST (Same.row_slot F₄ (by rw [efs]; omega_using [hio]) (by rw [efs]; omega_using [hio]) (.inl (by omega_using [])) (by omega_using [eP, hAF]) hfit32)
      (Same.below O₅ (by rw [efs]; omega_using [hio]) (by omega_using [hn2, he, hn, hf16, ke, eMd, efs, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32]) hfit32)
      (Same.row_far F₆ (by rw [eds]; omega_using [hio]) (by rw [efs]; omega_using [hio]) (.inl far) (by omega_using [eP, hAF]) hfit32)
      (Same.row_far F₇ (by rw [eds]; omega_using [hio]) (by rw [efs]; omega_using [hio]) (.inl far) (by omega_using [eP, hAF]) hfit32)
  have Sg₇ : Same B (AF + fgSz + (o + 4)) fgSz (nw len + 1) s₄.mem t.mem :=
    ((Same.below O₅ (by rw [efs]; omega_using [hio]) (by omega_using [hn2, he, hn, hf16, ke, eMd, efs, hAF, hAD, hn20, hd20, far, hAF32, hfit32, hdit32, hAD32]) hfit32).trans
      (Same.row_far F₆ (by rw [eds]; omega_using [hio]) (by rw [efs]; omega_using [hio]) (.inl far) (by omega_using [eP, hAF]) hfit32)).trans
      (Same.row_far F₇ (by rw [eds]; omega_using [hio]) (by rw [efs]; omega_using [hio]) (.inl far) (by omega_using [eP, hAF]) hfit32)
  have Sd₇ : Same B (AD + deSz + o) deSz (nw len + 1) s₆.mem t.mem :=
    Same.row_slot F₇ (by rw [eds]; omega_using [hio]) (by rw [eds]; omega_using [hio]) (.inl (by omega_using [])) (by omega_using [eP, hAD]) hdit32
  have Sp₇ : Same B (AD + deSz + 16) deSz (nw len + 1) s.mem t.mem :=
    Sp₆.trans (Same.row_slot F₇ (by rw [eds]; omega_using [hio]) (by rw [eds]) (.inr (by omega_using [hio])) (by omega_using [eP, hAD]) hdit32)
  refine ⟨H₇, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (K₁.trans (K₂.mono (by decide))).trans ((((K₃.mono (by decide)).trans (K₄.mono (by decide))).trans
      ((K₅.mono (by decide)).trans (K₆.mono (by decide)))).trans (K₇.mono (by decide)))
  · have hb4 : rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 4) = AF := by rw [← hA]; rfl
    have hb11 : rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 11) = AD := by rw [← hD]; rfl
    refine ((((((O₁.unch.trans O₂.unch).trans (F₃.unch (by rw [efs]; omega_using [hio]))).trans
      (F₄.unch (by rw [efs]; omega_using [hio]))).trans O₅.unch).trans (F₆.unch (by rw [eds]; omega_using [hio]))).trans
      (F₇.unch (by rw [eds]; omega_using [hio]))).cover ?_
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [batchWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hb4, hb11]
    rw [efs, eds] at *
    rcases hw with (((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | rfl) | (rfl | rfl)) | (rfl | rfl) <;> omega
  · rw [VG.Proof.Mont.w32, hT 100 (by omega_using [eMu])]; exact O₁.w32 (.inr (by omega_using [e16])) (by omega_using [])
  · rw [hT win (by omega_using [e16, eMu])]; exact M₁.d
  · rw [VG.Proof.Mont.w32, hT (win + 28) (by omega_using [e16, eMu]), ← Fiv]; exact O₁.w32 (.inr (by omega_using [])) (by omega_using [e16])
  · rw [hA, Sf₇.sval_eq, V₃]; rfl
  · rw [hA, Sg₇.sval_eq, V₄]; rfl
  · rw [hD, Sd₇.sval_eq, V₆]; rfl
  · rw [hD, V₇]; rfl
  · rw [hD, Sp₇.sv, Fp]

end VG.Proof.Rsa.X86.InvBatchRt.F

/-! ## The fused batches on i686: the batches in turn

`RunAt`: the state of the first `j` batches, the reference run `W32.invRun 30 p iv X` for `f, g`
and `deRunL` for `d, e`, which `FBody` runs the batches through.
-/

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx kw_eq bodyWrites)
open VG.Proof.Rsa.Divstep (oddInput)
open VG.Impl.Rsa.X86.Keys (seqs)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- A run's `d, f, g` do not depend on the coefficients' modular inverse. -/
theorem invRun_m (N : Nat) (p m m' x : Int) : ∀ k,
    (Divstep.W32.invRun N p m x k).d = (Divstep.W32.invRun N p m' x k).d ∧
    (Divstep.W32.invRun N p m x k).f = (Divstep.W32.invRun N p m' x k).f ∧
    (Divstep.W32.invRun N p m x k).g = (Divstep.W32.invRun N p m' x k).g
  | 0 => ⟨rfl, rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := invRun_m N p m m' x k
    simp only [Divstep.W32.invRun, Divstep.W32.batch]
    rw [h1, h2, h3]
    exact ⟨rfl, rfl, rfl⟩

/-- The reference run's state after `j` batches. -/
abbrev rs (p iv x j : Nat) : Divstep.W32.IState := Divstep.W32.invRun 30 p iv (oddInput p x) j
abbrev rde (p iv x j : Nat) : Int × Int := Divstep.deRunL p iv (oddInput p x) j

/-- The state of the first `j` batches at byte `i`. -/
abbrev RunAt (len : Nat) (B : Addr) (p iv x j i : Nat) (s : State) : Prop :=
  FAt len B p iv (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g (rde p iv x j).1 (rde p iv x j).2 i s

end VG.Proof.Rsa.X86.InvBatchRt.F
