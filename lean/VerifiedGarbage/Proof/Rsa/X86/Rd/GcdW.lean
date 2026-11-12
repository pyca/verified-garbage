module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatchStep
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Update
import VerifiedGarbage.Proof.Divstep.Tc32
import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FFinish
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FInit
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
import Mathlib.Algebra.Order.Ring.Abs

/-! # Prime recovery's GCD on i686: #4989's fused `f, g` rows alone

`batchG_ok`: a batch of the GCD (`RecoverDetRt.batchG`), the window's thirty divsteps applied to
`f, g` in rows of `n` words (`n = w + 2` for the recovery's narrow `w`), from the elements' byte `i`
to byte `o`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover.G

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx MatrixAt rv_h0)
open VG.Proof.Rsa.X86.InvBatchRt.F
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Proof.Rsa.Divstep (oddInput)

variable {B : Addr} {Z len N n : Nat}

/-- `δ`, `f` and `g` at byte `i` of the interleaved elements, rows of `n` words. -/
structure GAt (len n : Nat) (B : Addr) (dl f g : Int) (i : Nat) (s : State) : Prop where
  dl : s.mem.readW (off B win) 32 = BitVec.ofInt 32 dl
  f : sval s.mem B (rv (kw len) { arr := fgArr } n + fgSz + i) fgSz n = f
  g : sval s.mem B (rv (kw len) { arr := fgArr } n + fgSz + (i + 4)) fgSz n = g

/-- What a batch writes: the window and the matrix, the coefficients' masks, and the rows. -/
def gWrites (len n : Nat) : List (Nat × Nat) :=
  [(win, 88), (160, 48), (rv (kw len) { arr := fgArr } n, fgSz * (n + 2))]


open VG.Impl.Rsa.X86.RecoverRt (wid) in
/-- A batch of the GCD from byte `i` to byte `o`: the window's thirty divsteps applied to `f, g`. -/
theorem batchG_ok {s : State} (h : Bx wid s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    (hfit : rv (kw len) { arr := fgArr } n + fgSz * (n + 2) < Z) {i o : Nat}
    (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) {dl f g : Int}
    (G : GAt len n B dl f g i s) (hdl : |dl| + 64 < 2 ^ 30) (hfo : f % 2 = 1)
    (hf' : InRange n (fNext dl f g)) (hg' : InRange n (gNext dl f g)) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.batchG (i = 0)) s fun t =>
      Bx wid t B Z len N n ∧ Keeps wordClob s t ∧ Unch B (gWrites len n) s.mem t.mem ∧
      VG.Proof.Mont.w32 t.mem B 100 = VG.Proof.Mont.w32 s.mem B 100 ∧
      GAt len n B (bT dl f g).d (fNext dl f g) (gNext dl f g) o t := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have e16 : win = 16 := rfl; have eMu : sMu = 160 := rfl; have eP : sP = 176 := rfl
  have efs : fgSz = 16 := rfl
  have hAF : rv (kw len) { arr := fgArr } n = 160 + 4 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, fgArr]; omega
  have hfg0 : fg0 len = rv (kw len) { arr := fgArr } n + fgSz := by simp only [fg0, rv]; omega
  have Fdl := G.dl; have Ff := G.f; have Fg := G.g
  have hi8 : i ≤ 8 := by omega
  have hoi : (i + 4 ≤ o ∨ o + 4 ≤ i) ∧ (i + 4 + 4 ≤ o ∨ o + 4 ≤ i + 4) ∧ (i + 4 ≤ o + 4 ∨ o + 4 + 4 ≤ i) ∧
      (i + 4 + 4 ≤ o + 4 ∨ o + 4 + 4 ≤ i + 4) := by omega
  generalize hA : rv (kw len) { arr := fgArr } n = AF at hAF hfg0 Ff Fg hfit
  set T := bT dl f g with hT
  have bnd := Divstep.msteps_bnd dl f g 30
  simp only [Divstep.MSt.bnd] at bnd
  have code : VG.Impl.Rsa.X86.RecoverDetRt.batchG (i = 0) = seqs [.block (startF wid i),
      VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, .block coefMasks,
      row wid false fgArr fgSz o [⟨i, win + 12, sMu⟩, ⟨i + 4, win + 16, sMu + 4⟩]
        [⟨i, win + 12, sMu⟩, ⟨i + 4, win + 16, sMu + 4⟩],
      row wid false fgArr fgSz (o + 4) [⟨i, win + 20, sMu + 8⟩, ⟨i + 4, win + 24, sMu + 12⟩]
        [⟨i, win + 20, sMu + 8⟩, ⟨i + 4, win + 24, sMu + 12⟩]] := by
    rcases hio with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [code]
  simp only [seqs]
  -- The window.
  have hfw : ((s.mem.readW (off B (fg0 len + i)) 32).toNat : Int) % 2 ^ 32 = f % 2 ^ 32 := by
    have := sval_low s.mem B (AF + fgSz + i) fgSz n
    rw [Ff] at this; rw [hfg0]; exact this
  have hgw : ((s.mem.readW (off B (fg0 len + (i + 4))) 32).toNat : Int) % 2 ^ 32 = g % 2 ^ 32 := by
    have := sval_low s.mem B (AF + fgSz + (i + 4)) fgSz n
    rw [Fg] at this; rw [hfg0]; exact this
  refine VG.Proof.Rsa.X86.InvBatchRt.seq_assoc (WP.seq (WP.mono (windowF_ok h (by omega) G.dl hfw hgw hdl hfo)
    fun s₁ ⟨H₁, M₁, K₁, O₁⟩ => ?_))
  -- The masks.
  refine WP.seq (WP.mono (coefMasks_ok H₁) fun s₂ ⟨H₂, V₂, O₂, K₂⟩ => ?_)
  have c₂ : ∀ d, d + 4 ≤ win + 28 → win + 12 ≤ d →
      s₂.mem.readW (off B d) 32 = s₁.mem.readW (off B d) 32 := fun d h1 h2 => hdr_out O₂ (.inl (by omega)) (by omega)
  have Sf₂ : Same B (AF + fgSz + i) fgSz (n + 1) s.mem s₂.mem :=
    (Same.below O₁ (by omega) (by omega) (by omega)).trans (Same.below O₂ (by omega) (by omega) (by omega))
  have Sg₂ : Same B (AF + fgSz + (i + 4)) fgSz (n + 1) s.mem s₂.mem :=
    (Same.below O₁ (by omega) (by omega) (by omega)).trans (Same.below O₂ (by omega) (by omega) (by omega))
  have mk₂ : ∀ j < 4, s₂.mem.readW (off B (sMu + 4 * j)) 32 = maskW (s₂.mem.readW (off B (win + 12 + 4 * j)) 32) :=
    fun j hj => by rw [V₂ j hj, c₂ _ (by omega) (by omega)]
  have hu₂ : s₂.mem.readW (off B (win + 12)) 32 = BitVec.ofInt 32 T.u := by rw [c₂ _ (by omega) (by omega)]; exact M₁.u
  have hv₂ : s₂.mem.readW (off B (win + 16)) 32 = BitVec.ofInt 32 T.v := by rw [c₂ _ (by omega) (by omega)]; exact M₁.v
  have hq₂ : s₂.mem.readW (off B (win + 20)) 32 = BitVec.ofInt 32 T.q := by rw [c₂ _ (by omega) (by omega)]; exact M₁.q
  have hr₂ : s₂.mem.readW (off B (win + 24)) 32 = BitVec.ofInt 32 T.r := by rw [c₂ _ (by omega) (by omega)]; exact M₁.r
  -- The row of `f`.
  have tsF : ∀ {m : Mem} {c₁ c₂ m₁ m₂ : Nat} (o' : Nat), o' + 4 ≤ fgSz → (i + 4 ≤ o' ∨ o' + 4 ≤ i) →
      (i + 4 + 4 ≤ o' ∨ o' + 4 ≤ i + 4) → c₁ + 4 ≤ sP → c₂ + 4 ≤ sP → m₁ + 4 ≤ sP → m₂ + 4 ≤ sP →
      m.readW (off B m₁) 32 = maskW (m.readW (off B c₁) 32) → m.readW (off B m₂) 32 = maskW (m.readW (off B c₂) 32) →
      TermsOk m B AF fgSz o' [⟨i, c₁, m₁⟩, ⟨i + 4, c₂, m₂⟩] := by
    intro m c₁ c₂ m₁ m₂ o' h1 h2 h3 h4 h5 h6 h7 h8 h9 t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨show c₁ + 4 ≤ AF by omega, show m₁ + 4 ≤ AF by omega, show i + 4 ≤ fgSz by rw [efs]; omega,
        h2, .inl h4, .inl h6, h8⟩
    · exact ⟨show c₂ + 4 ≤ AF by omega, show m₂ + 4 ≤ AF by omega, show i + 4 + 4 ≤ fgSz by rw [efs]; omega,
        h3, .inl h5, .inl h7, h9⟩
  have huv : |T.u| + |T.v| ≤ 2 ^ 30 := bnd.1
  have hqr : |T.q| + |T.r| ≤ 2 ^ 30 := bnd.2
  have ts₂ : TermsOk s₂.mem B AF fgSz o [⟨i, win + 12, sMu⟩, ⟨i + 4, win + 16, sMu + 4⟩] := by
    refine tsF o (by rw [efs]; omega) hoi.1 hoi.2.1 (by omega) (by omega) (by omega) (by omega) ?_ ?_
    · simpa using mk₂ 0 (by omega)
    · simpa using mk₂ 1 (by omega)
  have rf := rowTwo_ok H₂ hn2 he (arr := fgArr) (sz := fgSz) (o := o) (t₁ := ⟨i, win + 12, sMu⟩)
    (t₂ := ⟨i + 4, win + 16, sMu + 4⟩) (Or.inl rfl) (by rw [efs]; omega) (by rw [hA]; omega) (by rw [hA]; omega)
    (by rw [hA]; exact ts₂) hu₂ hv₂ huv
    (by dsimp only; rw [hA, Sf₂.sval_eq, Sg₂.sval_eq, Ff, Fg]; exact hf')
  refine WP.seq (WP.mono rf fun s₃ ⟨H₃, K₃, F₃, V₃⟩ => ?_)
  rw [hA] at F₃ V₃
  dsimp only at V₃
  rw [Sf₂.sval_eq, Sg₂.sval_eq, Ff, Fg] at V₃
  have hAF32 : AF ≤ 2 ^ 32 := by omega
  have hfit32 : AF + fgSz * (n + 2) ≤ 2 ^ 32 := by omega
  -- The row of `g`.
  have Sf₃ : Same B (AF + fgSz + i) fgSz (n + 1) s.mem s₃.mem :=
    Sf₂.trans (Same.row_slot F₃ (by rw [efs]; omega) (by rw [efs]; omega) hoi.1 (by omega) hfit32)
  have Sg₃ : Same B (AF + fgSz + (i + 4)) fgSz (n + 1) s.mem s₃.mem :=
    Sg₂.trans (Same.row_slot F₃ (by rw [efs]; omega) (by rw [efs]; omega) hoi.2.1 (by omega) hfit32)
  have h₃ : ∀ d, d + 4 ≤ sP → s₃.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd =>
    hdr_row F₃ (by omega) (.inl hd) hAF32
  have ts₃ : TermsOk s₃.mem B AF fgSz (o + 4) [⟨i, win + 20, sMu + 8⟩, ⟨i + 4, win + 24, sMu + 12⟩] := by
    refine tsF (o + 4) (by rw [efs]; omega) hoi.2.2.1 hoi.2.2.2 (by omega) (by omega) (by omega) (by omega) ?_ ?_
    · rw [h₃ (sMu + 8) (by omega), h₃ (win + 20) (by omega)]; simpa using mk₂ 2 (by omega)
    · rw [h₃ (sMu + 12) (by omega), h₃ (win + 24) (by omega)]; simpa using mk₂ 3 (by omega)
  have rg := rowTwo_ok H₃ hn2 he (arr := fgArr) (sz := fgSz) (o := o + 4) (t₁ := ⟨i, win + 20, sMu + 8⟩)
    (t₂ := ⟨i + 4, win + 24, sMu + 12⟩) (Or.inl rfl) (by rw [efs]; omega) (by rw [hA]; omega) (by rw [hA]; omega)
    (by rw [hA]; exact ts₃) (by rw [h₃ (win + 20) (by omega)]; exact hq₂) (by rw [h₃ (win + 24) (by omega)]; exact hr₂) hqr
    (by dsimp only; rw [hA, Sf₃.sval_eq, Sg₃.sval_eq, Ff, Fg]; exact hg')
  refine WP.mono rg fun t ⟨H₄, K₄, F₄, V₄⟩ => ?_
  rw [hA] at F₄ V₄
  dsimp only at V₄
  rw [Sf₃.sval_eq, Sg₃.sval_eq, Ff, Fg] at V₄
  have hT₄ : ∀ d, d + 4 ≤ sP → t.mem.readW (off B d) 32 = s₂.mem.readW (off B d) 32 := fun d hd => by
    rw [hdr_row F₄ (by omega) (.inl hd) hAF32, h₃ d hd]
  have hT : ∀ d, d + 4 ≤ sMu → t.mem.readW (off B d) 32 = s₁.mem.readW (off B d) 32 := fun d hd => by
    rw [hT₄ d (by omega), hdr_out O₂ (.inl hd) (by omega)]
  have Sf₄ : Same B (AF + fgSz + o) fgSz (n + 1) s₃.mem t.mem :=
    Same.row_slot F₄ (by rw [efs]; omega) (by rw [efs]; omega) (by omega) (by omega) hfit32
  refine ⟨H₄, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · exact (K₁.trans (K₂.mono (by decide))).trans ((K₃.mono (by decide)).trans (K₄.mono (by decide)))
  · refine (((O₁.unch.trans O₂.unch).trans (F₃.unch (by rw [efs]; omega))).trans
      (F₄.unch (by rw [efs]; omega))).cover ?_
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [gWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hA]
    rw [efs] at *
    rcases hw with ((rfl | rfl) | rfl | rfl) | rfl | rfl <;> dsimp only <;> omega
  · rw [VG.Proof.Mont.w32, hT 100 (by omega)]; exact O₁.w32 (.inr (by omega)) (by omega)
  · rw [hT win (by omega)]; exact M₁.d
  · rw [hA, Sf₄.sval_eq, V₃]; rfl
  · rw [hA, V₄]; rfl

/-! ## The batches in turn -/

/-- `δ, f, g`'s bounds after `j` batches: no inverse word or `1 < p` needed (only `d, e` need them). -/
theorem dfg_bounds {p iv x cap : Nat} (odd : p % 2 = 1) (pc : p ≤ cap) (xc : oddInput p x ≤ cap) (j : Nat) :
    |(rs p iv x j).d| ≤ 1 + 2 * (30 * j : Nat) ∧ (rs p iv x j).f % 2 = 1 ∧ |(rs p iv x j).f| ≤ cap ∧
      |(rs p iv x j).g| ≤ cap := by
  have oddI : (p : Int) % 2 = 1 := by exact_mod_cast odd
  have dfg := (Divstep.W32.invRun_dfg (N := 30) (m := (iv : Int)) (x := (oddInput p x : Int)) oddI j)
  have pair := Divstep.W32.divsteps_le (M := (cap : Int)) (d := 1) (f := (p : Int)) (g := (oddInput p x : Int))
    (by decide) oddI (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast pc)
    (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast xc) (30 * j)
  have delta := Divstep.W32.divsteps_d (1, (p : Int), (oddInput p x : Int)) (30 * j)
  have dd : (rs p iv x j).d = (Divstep.divsteps (30 * j) (1, (p : Int), (oddInput p x : Int))).1 := by
    simp only [rs]; rw [← dfg.1]
  have df : (rs p iv x j).f = (Divstep.divsteps (30 * j) (1, (p : Int), (oddInput p x : Int))).2.1 := by
    simp only [rs]; rw [← dfg.1]
  have dg : (rs p iv x j).g = (Divstep.divsteps (30 * j) (1, (p : Int), (oddInput p x : Int))).2.2 := by
    simp only [rs]; rw [← dfg.1]
  refine ⟨?_, dfg.2, by rw [df]; exact pair.1, by rw [dg]; exact pair.2⟩
  rw [dd]; simpa using delta

/-- `δ, f, g` after the first `j` batches of the reference run, at byte `i`. -/
abbrev GRun (len n : Nat) (B : Addr) (p iv x j i : Nat) (s : State) : Prop :=
  GAt len n B (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g i s

open VG.Impl.Rsa.X86.RecoverRt (wid) in
theorem stepG_ok {s : State} (h : Bx wid s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    (hfit : rv (kw len) { arr := fgArr } n + fgSz * (n + 2) < Z) {i o : Nat}
    (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) {p iv x j : Nat} (odd : p % 2 = 1)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n))
    (hj : j < 1500) (F : GRun len n B p iv x j i s) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.batchG (i = 0)) s fun t =>
      Bx wid t B Z len N n ∧ Keeps wordClob s t ∧ Unch B (gWrites len n) s.mem t.mem ∧
      VG.Proof.Mont.w32 t.mem B 100 = VG.Proof.Mont.w32 s.mem B 100 ∧ GRun len n B p iv x (j + 1) o t := by
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  have b₀ := dfg_bounds (iv := iv) (cap := p + x) odd (by omega) ox j
  have b₁ := dfg_bounds (iv := iv) (cap := p + x) odd (by omega) ox (j + 1)
  obtain ⟨bd, fo, -, -⟩ := b₀
  obtain ⟨-, -, f1, g1⟩ := b₁
  have pcI : (p : Int) + x < 2 ^ (32 * n) * 2 := by
    have : (2 : Int) ^ (32 * n) = ((2 ^ (32 * n) : Nat) : Int) := by push_cast; rfl
    rw [this]; omega
  have big : (2 : Int) ^ (32 * n) * 2 ≤ 2 ^ (32 * n) * 2 ^ 31 :=
    Int.mul_le_mul_of_nonneg_left (by decide) (Int.le_of_lt (two_pow_pos' _))
  have hfn : (rs p iv x (j + 1)).f = fNext (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g := rfl
  have hgn : (rs p iv x (j + 1)).g = gNext (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g := rfl
  have hdn : (rs p iv x (j + 1)).d = (bT (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g).d := by
    show (Divstep.W32.batch 30 p iv (rs p iv x j)).d = _
    rw [Divstep.W32.batch_d]; rfl
  have range : ∀ y : Int, |y| ≤ p + x → InRange n y := fun y hy => by
    rw [abs_le] at hy; push_cast at hy; exact ⟨by omega, by omega⟩
  have hd : |(rs p iv x j).d| + 64 < 2 ^ 30 := by
    have : (1 + 2 * (30 * j : Nat) : Int) ≤ 1 + 60 * 1500 := by push_cast; omega
    omega
  refine WP.mono (batchG_ok h hn2 he hfit hio F hd fo (by rw [← hfn]; exact range _ f1)
    (by rw [← hgn]; exact range _ g1)) fun t ⟨Ht, Kt, Ut, Ct, Ft⟩ => ⟨Ht, Kt, Ut, Ct, ?_⟩
  show GAt len n B _ _ _ o t
  rw [hdn, hfn, hgn]
  exact Ft

theorem Bx.keepHighN {L : Lay} {s t : State} (h : Bx L s B Z len N n) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (ho : halfSlot + 4 ≤ o) (hc : o + c ≤ Z) : Bx L t B Z len N n := by
  have nw := h.nowrap
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega)), ⟨fun j d hd => ?_, ?_, h.slots.small, h.slots.pos⟩, h.room⟩
  · have := VG.Proof.Rsa.X86.InvBatchRt.slot_le hd
    rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inl (by omega)) (by omega)]
    exact h.slots.half

/-- The state survives the counter's store. -/
theorem GAt.keep100 {dl f g : Int} {i : Nat} {s z : State} (F : GAt len n B dl f g i s) (hi : i ≤ 8)
    (O : Outside B 100 4 s.mem z.mem) (hfg : rv (kw len) { arr := fgArr } n + fgSz * (n + 2) ≤ 2 ^ 32)
    (hA : 104 ≤ rv (kw len) { arr := fgArr } n) : GAt len n B dl f g i z := by
  have e16 : win = 16 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdr_out O (.inl (by omega)) (by omega)]; exact F.dl
  · rw [(Same.below O (by unfold fgSz; omega) hA hfg).sval_eq]; exact F.f
  · rw [(Same.below O (by unfold fgSz; omega) hA hfg).sval_eq]; exact F.g

open VG.Impl.Rsa.X86.RecoverRt (wid) in
/-- The loop of double batches, `K` of them. -/
theorem loopG_ok {s : State} (h : Bx wid s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    (hfit : rv (kw len) { arr := fgArr } n + fgSz * (n + 2) < Z)
    {p iv x K : Nat} (odd : p % 2 = 1)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) (F : GRun len n B p iv x 0 0 s)
    (hK1 : 1 ≤ K) (hK : 2 * K < 1500) (cnt : VG.Proof.Mont.w32 s.mem B 100 = K) :
    WP isa (.loop (seqs [VG.Impl.Rsa.X86.RecoverDetRt.batchG true, VG.Impl.Rsa.X86.RecoverDetRt.batchG false,
      .block [.mov .esi (.mem (sc 100)), VG.Impl.Weierstrass.X86.decCounter, .store (sc 100) .esi,
        VG.Impl.Weierstrass.X86.testCounter]]) .ne) s fun t =>
      Bx wid t B Z len N n ∧ Keeps wordClob s t ∧ Unch B (gWrites len n) s.mem t.mem ∧
      GRun len n B p iv x (2 * K) 0 t := by
  have hn := h.nowrap
  have hAF : rv (kw len) { arr := fgArr } n = 160 + 4 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, fgArr]; omega
  have efs : fgSz = 16 := rfl
  have e96 : halfSlot = 96 := rfl
  refine WP.loop (M := isa) (fun rem u => ∃ k, k + rem = K ∧ 0 < rem ∧ Bx wid u B Z len N n ∧ Keeps wordClob s u ∧
    Unch B (gWrites len n) s.mem u.mem ∧ VG.Proof.Mont.w32 u.mem B 100 = K - k ∧ GRun len n B p iv x (2 * k) 0 u)
    ?_ K s ⟨0, by omega, by omega, h, Keeps.refl _ _, Unch.refl _ _ _, by rw [cnt]; omega, by simpa using F⟩
  rintro rem u ⟨k, hk, hr, Hu, Ku, Uu, Cu, Fu⟩
  simp only [seqs]
  refine WP.seq (WP.mono (stepG_ok Hu hn2 he hfit (.inl ⟨rfl, rfl⟩) odd pc xc (by omega) Fu)
    fun u₁ ⟨H₁, K₁, U₁, C₁, F₁⟩ => ?_)
  refine WP.seq (WP.mono (stepG_ok H₁ hn2 he hfit (.inr ⟨rfl, rfl⟩) odd pc xc (by omega) F₁)
    fun u₂ ⟨H₂, K₂, U₂, C₂, F₂⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok H₂.ws.ws.workspace (d := 100) (by omega)
    (j := K - k) (by omega) (by omega) (by rw [C₂, C₁, Cu])) fun z ⟨c, zf, K₃, O₃⟩ => ?_
  have Hz : Bx wid z B Z len N n := Bx.keepHighN H₂ K₃ (by decide) (by decide) O₃ (by omega) (by omega)
  have Fz := F₂.keep100 (by omega) O₃ (by omega) (by rw [hAF]; omega)
  have Kz : Keeps wordClob s z := ((Ku.trans K₁).trans K₂).trans (K₃.mono (by decide))
  have Uz : Unch B (gWrites len n) s.mem z.mem :=
    ((((Uu.trans U₁).trans U₂).trans O₃.unch).cover fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with ((h1 | h1) | h1) | h1
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · subst h1; exact ⟨(win, 88), by simp [gWrites], by decide, by decide⟩)
  by_cases last : k + 1 = K
  · left
    refine ⟨?_, Hz, Kz, Uz, ?_⟩
    · change z.zf.map (!·) = some false
      rw [zf, show K - k - 1 = 0 by omega]; rfl
    · rw [show 2 * K = 2 * k + 1 + 1 by omega]; exact Fz
  · right
    refine ⟨?_, rem - 1, by omega, k + 1, by omega, by omega, Hz, Kz, Uz, by rw [c]; omega, ?_⟩
    · change z.zf.map (!·) = some true
      rw [zf, decide_eq_false (show ¬ K - k - 1 = 0 by omega)]; rfl
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]; exact Fz

/-- The reference run has converged after `j ≥ 3 (n + 1)` batches, for `p, x < 2^(32 n)`: `g = 0` and
`|f| = gcd(p, x)`. Its proof (`Rd/GcdDone.lean`, from `done_words`) imports the bound's heavy algebra, which
the instance keeps out of the proofs that use it. -/
class GcdDone : Prop where
  done : ∀ {p iv x n j : Nat}, p % 2 = 1 → p < 2 ^ (32 * n) → x < 2 ^ (32 * n) → 3 * (n + 1) ≤ j →
    (rs p iv x j).g = 0 ∧ (rs p iv x j).f.natAbs = Nat.gcd p x

theorem oddInput_le_two {m x R : Nat} (hm : m < R) (hx : x < R) : oddInput m x < 2 * R := by
  unfold oddInput; split <;> omega

/-! ## The finish -/

theorem keep_outside {B : Addr} {w j : Nat} {m m' : Mem} (k : VG.Proof.Rsa.X86.Keys.Keep B w [j] [] m m') :
    Outside B (VG.Proof.Rsa.X86.Keys.arr w j) (VG.Proof.Rsa.X86.Keys.S w) m m' := fun x hx =>
  k x fun r hr => by
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    subst hr; exact hx

theorem rv_j (len n j : Nat) : rv (kw len) { arr := j } n = 160 + j * (4 * kw len + 8) := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset]; omega

theorem arr_rv (len n j : Nat) : VG.Proof.Rsa.X86.Keys.arr (kw len) j = rv (kw len) { arr := j } n := by
  rw [rv_j]; simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [show 4 * (kw len + 2) = 4 * kw len + 8 by omega]

open VG.Impl.Rsa.X86.RecoverRt (wid) in
/-- `|f|` into `[12]` (`n` words) from `f` at byte 8 of the rows, through `[14]`. -/
theorem finishG_ok {s : State} (h : Bx wid s B Z len N n) (hn2 : 2 ≤ n) (hnk : n ≤ kw len / 2 + 1) {f : Int}
    (F : sval s.mem B (rv (kw len) { arr := fgArr } n + fgSz + 8) fgSz n = f) (hb : |f| < 2 ^ (32 * n)) :
    WP isa (seqs [gather wid fgArr fgSz 8 { arr := 14 }, VG.Impl.Rsa.X86.KeyRt.zeroWide wid 12,
      VG.Impl.Rsa.X86.InvBatchRt.chain wid .sbb { arr := 12 } { arr := 12 } { arr := 14 } (nBytes .edx 0),
      .block (maskAt wid { arr := 14, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
      selIn wid { arr := 12 } { arr := 14 } (nBytes .edi 0)]) s fun z =>
      Bx wid z B Z len N n ∧ val32 z.mem B (rv (kw len) { arr := 12 } n) n = f.natAbs ∧
      Keeps wordClob s z ∧
      Unch B [(rv (kw len) { arr := 12 } n, 4 * kw len + 8), (rv (kw len) { arr := 14 } n, 4 * kw len + 8)]
        s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  have r4 := rv_j len n 4; have r12 := rv_j len n 12; have r14 := rv_j len n 14
  have efs : fgSz = 16 := rfl
  have hfg : rv (kw len) { arr := fgArr } n = rv (kw len) { arr := 4 } n := rfl
  have h41 : rv (kw len) { arr := 14, half := 1 } n = rv (kw len) { arr := 14 } n + 4 * n := by
    simp only [rv]; omega
  simp only [seqs]
  -- `[14] = f`, `n + 1` words.
  refine WP.seq (WP.mono (gather_ok h (arr := fgArr) (sz := fgSz) (x := 8) (dst := { arr := 14 }) (by decide)
    (by rw [hfg, r4, efs]; omega) (by omega) (.inr (by rw [hfg, r4, efs]; omega)))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  have hR : -((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) ≤ f ∧ f < ((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) := by
    rw [abs_lt] at hb; push_cast
    have : (2 : Int) ^ (32 * n) ≤ 2 ^ (32 * n) * 2 ^ 31 :=
      le_mul_of_one_le_right (Int.le_of_lt (two_pow_pos' _)) (by decide)
    omega
  have rep : Rep (2 ^ (32 * n) * 2 ^ 31) (val32 s₁.mem B (rv (kw len) { arr := 14 } n) (n + 1)) f := by
    rw [V₁, ← F]; exact rep_sval (by rw [F]; exact hR.1) (by rw [F]; exact hR.2)
  -- `[12] = 0`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok H₁.ws (j := 12) (by have := H₁.room; omega))
    fun s₂ ⟨W₂, k₂, Z₂, K₂⟩ => ?_)
  have O₂ := keep_outside k₂
  rw [arr_rv len n] at O₂ Z₂
  simp only [VG.Proof.Rsa.X86.Keys.S] at O₂
  have H₂ : Bx wid s₂ B Z len N n := H₁.keep K₂ (by decide) (by decide) O₂ (by omega) (by omega)
  have Z₂' : val32 s₂.mem B (rv (kw len) { arr := 12 } n) n = 0 := by
    have := val32_append s₂.mem B (rv (kw len) { arr := 12 } n) n (kw len + 1 - n)
    rw [show n + (kw len + 1 - n) = kw len + 1 by omega, Z₂] at this; omega
  -- `[12] = -[14]`, `n` words.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.chainSub_ok H₂ (o := { arr := 12 }) (a := { arr := 12 }) (b := { arr := 14 }) (e := 0)
    (by decide) rfl (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (.inl (by omega)))
    fun s₃ ⟨H₃, O₃, ⟨c, _, V₃⟩, K₃⟩ => ?_)
  simp only [Nat.add_zero] at O₃ V₃
  rw [Z₂', Nat.zero_add, O₂.val32 (by omega) (by omega)] at V₃
  -- The selection of `[14]` where `f` is not negative.
  refine WP.seq (VG.Proof.Rsa.X86.InvBatchRt.maskAt_ok H₃ (x := { arr := 14, half := 1 }) (by omega) fun s₄ K₄ m₄ c₄ => ?_)
  rw [h41, O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega)] at c₄
  refine wp_logicS (.inr rfl) rfl fun s₅ U₅ => WP.block_nil ?_
  have K₅ : Keeps [.eax, .ebx, .ecx, .edx] s₃ s₅ := K₄.trans (U₅.keeps.mono (by decide))
  have m₅ : s₅.mem = s₃.mem := by rw [U₅.mem, m₄]
  have H₅ : Bx wid s₅ B Z len N n := H₃.keep K₅ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₅]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have sign := top_sign rep
  have mask : s₅.gpr .ecx = cmask (!decide (f < 0)) := by
    rw [U₅.gpr, ite_eq_right (by decide), c₄]
    simp only [cmask]
    by_cases hf : f < 0
    · rw [ite_eq_left (sign.mpr hf)]; simp only [hf, decide_true, Bool.not_true]; decide
    · rw [ite_eq_right (fun e => hf (sign.mp e))]; simp only [hf, decide_false, Bool.not_false]; decide
  refine WP.mono (VG.Proof.Rsa.X86.InvBatchRt.selIn_ok H₅ (o := { arr := 12 }) (a := { arr := 14 }) (e := 0) mask (by decide) (by omega)
    (by omega) (.inl (by omega))) fun z ⟨Hz, Oz, Vz, Kz⟩ => ⟨Hz, ?_, ?_, ?_⟩
  · simp only [Nat.add_zero] at Vz
    rw [Vz, m₅, O₃.val32 (d := rv (kw len) { arr := 14 } n) (by omega) (by omega),
      O₂.val32 (d := rv (kw len) { arr := 14 } n) (by omega) (by omega)]
    have := VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _)
      (by exact_mod_cast rep.low) ⟨c, V₃⟩
    rw [← this]
    by_cases hf : f < 0 <;> simp [hf]
  · exact ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₅.mono (by decide))).trans (Kz.mono (by decide))
  · intro x hx
    have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    simp only [Nat.add_zero] at Oz
    rw [Oz x (by omega), m₅, O₃ x (by omega), O₂ x (by omega), O₁ x (by omega)]


/-! ## The start -/

open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
/-- `n`'s length as the narrow layout reads it, from the wide layout's: the same argument. -/
theorem lenNar {s : State} {Zw lenW Nw ln : Nat} (h : RtWs wid s B Zw lenW Nw)
    (e : ∀ a, kw (wid.toLen a) = kw lenW → kw (nar.toLen a) = kw ln) :
    VG.Proof.Rsa.X86.KeyRt.LenSrc nar s ln := by
  obtain ⟨a, la, ea, ca⟩ := h.lenArg
  exact ⟨a, la, e a ea, by rw [VG.Proof.Rsa.X86.KeyRt.lenOp_eq (L := nar) (by decide)]; exact ca.readSrc⟩

open VG.Proof.Bignum.X86.R2Words in
open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
/-- `gN`: rows of `w + 2` words, `w` the narrow length. -/
theorem gN_ok {s : State} (h : Bx wid s B Z len N) {ln : Nat} (hl : VG.Proof.Rsa.X86.KeyRt.LenSrc nar s ln)
    (hln : ln ≤ 4096) (hfit : 4 * (kw ln + 2) < 2 ^ 32) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverDetRt.gN) s fun t =>
      Bx wid t B Z len N (kw ln + 2) ∧ Keeps [.eax, .ecx, .edx] s t ∧ Outside B halfSlot 4 s.mem t.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have e96 : halfSlot = 96 := rfl
  rw [show VG.Impl.Rsa.X86.RecoverDetRt.gN = VG.Impl.Rsa.X86.KeyRt.bytesB nar .eax ++
    ([.alu .add .eax (.imm 8), .store (sc halfSlot) .eax] : List Instr) from rfl]
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok hl hln fun u K m c => ?_
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  have di : PtrAt u B .edi 0 := by
    rw [PtrAt, K.1 _ (by decide), RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  obtain ⟨hdi, aC, -⟩ := ptrRead ws di (d := halfSlot) (by omega)
  simp only [Nat.zero_add] at aC
  have wC := ws_write ws (y := halfSlot) (n := 4) (by omega)
  refine WP.mono (WP.keeps [.eax] (Q := fun v =>
    v.mem = u.mem.writeW (off B halfSlot) (BitVec.ofNat 32 (4 * (kw ln + 2)))) ?_ rfl) fun v ⟨mv, kv⟩ => ?_
  · xrun [sc, hdi, aC, wC]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, c]
    rw [show (8 : BitVec 32).toNat = 8 from rfl]
    congr 1
  · rw [m] at mv
    have KK : Keeps [.eax, .ecx, .edx] s v := (K.mono (by decide)).trans (kv.mono (by decide))
    have Om : Outside B halfSlot 4 s.mem v.mem := by rw [mv]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨⟨h.ws.keep KK (by decide) (by decide) (Om.mono (Nat.zero_le _) (by omega)),
      ⟨fun j d hd => ?_, ?_, by omega, by omega⟩, h.room⟩, KK, Om⟩
    · have := VG.Proof.Rsa.X86.InvBatchRt.slot_le hd
      rw [Om.w32 (.inl (by omega)) (by omega)]
      exact h.slots.addr j d hd
    · rw [mv, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]


open VG.Proof.Bignum.X86.R2Words in
open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
/-- The double batches' count, `(3 w + 6) / 2`. -/
theorem countG_ok {s : State} (h : Bx wid s B Z len N n) {ln : Nat} (hl : VG.Proof.Rsa.X86.KeyRt.LenSrc nar s ln)
    (hln : ln ≤ 4096) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.bytesB nar .eax ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax),
      .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 6), .shift .shr .eax 1,
      .store (sc 100) .eax] : List Instr))) s fun t =>
      Bx wid t B Z len N n ∧ t.mem = s.mem.writeW (off B 100) (BitVec.ofNat 32 ((3 * kw ln + 6) / 2)) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hw := kw_bound hln
  have hf16 := h.fits16
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok hl hln fun u K m c => ?_
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  have di : PtrAt u B .edi 0 := by
    rw [PtrAt, K.1 _ (by decide), RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  obtain ⟨hdi, aC, -⟩ := ptrRead ws di (d := 100) (by omega)
  simp only [Nat.zero_add] at aC
  have wC := ws_write ws (y := 100) (n := 4) (by omega)
  refine WP.mono (WP.keeps [.eax, .ecx] (Q := fun v =>
    v.mem = u.mem.writeW (off B 100) (BitVec.ofNat 32 ((3 * kw ln + 6) / 2))) ?_ rfl) fun v ⟨mv, kv⟩ => ?_
  · xrun [sc, hdi, aC, wC]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have l6 : (6 : BitVec 32).toNat = 6 := rfl
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, c, l6]
    generalize kw ln = q at *
    simp only [Nat.reducePow]
    have e1 : 4 * q / 4 = q := by omega
    rw [e1, Nat.mod_eq_of_lt (a := q + q) (by omega), Nat.mod_eq_of_lt (a := q + q + q) (by omega),
      Nat.mod_eq_of_lt (a := q + q + q + 6) (by omega), Nat.mod_eq_of_lt (a := (3 * q + 6) / 2) (by omega)]
    omega
  · rw [m] at mv
    have KK : Keeps [.eax, .ecx, .edx] s v := (K.mono (by decide)).trans (kv.mono (by decide))
    have Om : Outside B 100 4 s.mem v.mem := by rw [mv]; exact writeW32_outside _ _ _ (by omega)
    exact ⟨Bx.keepHighN h KK (by decide) (by decide) Om (by decide) (by omega), mv, KK⟩

theorem winOneN_ok {L : Lay} {s : State} (h : Bx L s B Z len N n) :
    WP isa (.block [.mov .eax (.imm 1), .store (sc win) .eax]) s fun t =>
      Bx L t B Z len N n ∧ t.mem = s.mem.writeW (off B win) (1 : BitVec 32) ∧ Keeps [.eax] s t := by
  have hZ := h.halfZ
  have e16 : win = 16 := rfl; have e96 : halfSlot = 96 := rfl
  refine wp_movS rfl fun u₁ V₁ _ => ?_
  have hs₁ := h.ws.ws.workspace.of_keeps V₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write (d := win) (n := 4) (by omega))
    fun u₂ V₂ => WP.block_nil ?_
  have m₂ : u₂.mem = s.mem.writeW (off B win) (1 : BitVec 32) := by rw [V₂.mem, V₁.mem, V₁.gpr]
  have K₂ : Keeps [.eax] s u₂ := V₁.keeps.trans (V₂.keeps _)
  have Om : Outside B win 4 s.mem u₂.mem := by rw [m₂]; exact writeW32_outside _ _ _ (by omega)
  exact ⟨h.keepLow K₂ (by decide) (by decide) Om (by decide), m₂, K₂⟩


/-! ## The operands -/

theorem zero_sub {m : Mem} {d k i j : Nat} (h : val32 m B d k = 0) (hij : i + j ≤ k) :
    val32 m B (d + 4 * i) j = 0 := by
  have e := val32_append m B d i (k - i)
  rw [show i + (k - i) = k by omega, h] at e
  have e2 := val32_append m B (d + 4 * i) j (k - i - j)
  rw [show j + (k - i - j) = k - i by omega] at e2
  have p := Nat.two_pow_pos (32 * i)
  have p2 := Nat.two_pow_pos (32 * j)
  have : val32 m B (d + 4 * i) (k - i) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * i) (k - i)) with z | z
    · exact z
    · have := Nat.mul_le_mul_left (2 ^ (32 * i)) z; omega
  omega

theorem low_ext {m : Mem} {d w v j : Nat} (hv : val32 m B d w = v) (hz : val32 m B (d + 4 * w) j = 0) :
    val32 m B d (w + j) = v := by
  rw [val32_append, hv, hz]; omega

open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
/-- The wide layout's context gives the narrow one's. -/
theorem rtNar {g : Geo} {s : State} (h : RtWs wid s g.B g.Z (16 * g.n + 24) 22) (up : g.n ≤ 128) :
    RtWs nar s g.B g.Z (8 * g.n + 8) VG.Impl.Rsa.X86.Recover.nArr := by
  obtain ⟨a, la, ea, ca⟩ := h.lenArg
  refine ⟨⟨h.ws.workspace, ?_, ?_, ?_⟩, ⟨a, la, ?_, ca⟩, h.wsArg, by omega, h.layLen⟩
  · rw [kw_nar, ← arrW_end]; have := h.ws.fits; rw [kw_wid] at this; exact this
  · rw [kw_nar]; simp only [VG.Impl.Rsa.X86.Recover.width]; omega
  · rw [kw_nar]; simp only [VG.Impl.Rsa.X86.Recover.width]; omega
  · simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      VG.Proof.Bignum.X86.PublicRt.wb, Spec.Rsa.modulusWords] at ea ⊢
    omega


theorem val32_low {m : Mem} {d k v : Nat} (h : val32 m B d (k + 1) = v) (hv : v < 2 ^ (32 * k)) :
    val32 m B d k = v := by
  rw [val32_succ] at h
  have p := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (w32 m B (d + 4 * k)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero] at h; exact h
  · have := Nat.mul_le_mul_left (2 ^ (32 * k)) e; omega

theorem parity_low {m : Mem} {d k x : Nat} (hk : 1 ≤ k) (h : val32 m B d k = x) : w32 m B d % 2 = x % 2 := by
  have e := val32_append m B d 1 (k - 1)
  rw [show 1 + (k - 1) = k by omega, h] at e
  simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reducePow] at e
  omega

open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
open VG.Impl.Rsa.X86.RecoverDetRt (aGm aGx) in
/-- The operands: `f = m` and `g = x` (`x + m` if `x` is even) in the rows, `w + 3` words each, from the
narrow `[aGm] = m` and `[aGx] = x`. -/
theorem operandsG_ok {g : Geo} {s : State} (h : Bx wid s g.B g.Z (16 * g.n + 24) 22 (g.w + 2)) (up : g.n ≤ 128)
    {m x : Nat} (hm : val32 s.mem g.B (VG.Proof.Rsa.X86.Keys.arr g.w aGm) g.w = m)
    (hx : val32 s.mem g.B (VG.Proof.Rsa.X86.Keys.arr g.w aGx) g.w = x) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.zeroWide wid 7, VG.Impl.Rsa.X86.KeyRt.copy nar 14 aGm,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid 8, VG.Impl.Rsa.X86.KeyRt.copy nar 16 aGx,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid 9,
      .block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0)),
      selIn wid { arr := 9 } { arr := 7 } (nBytes .edi 0),
      VG.Impl.Rsa.X86.InvBatchRt.chain wid .adc { arr := 8 } { arr := 8 } { arr := 9 } (nBytes .edx 1),
      scatter wid fgArr fgSz 0 { arr := 7 }, scatter wid fgArr fgSz 4 { arr := 8 }]) s fun t =>
      Bx wid t g.B g.Z (16 * g.n + 24) 22 (g.w + 2) ∧
      sv t.mem g.B (rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) + fgSz + 0) fgSz (g.w + 3) = m ∧
      sv t.mem g.B (rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) + fgSz + 4) fgSz (g.w + 3) = oddInput m x ∧
      Keeps wordClob s t ∧
      Unch g.B [(rv (kw (16 * g.n + 24)) { arr := 4 } (g.w + 2), 6 * (4 * kw (16 * g.n + 24) + 8)), (sP, 8)]
        s.mem t.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq (16 * g.n + 24)
  have eW : kw (16 * g.n + 24) = g.W := kw_wid g.n
  have ew : kw (8 * g.n + 8) = g.w := kw_nar g.n
  have eWw : g.W = 2 * g.w + 2 := rfl
  have w2 : 2 ≤ g.w := by show 2 ≤ 2 * g.n + 2; omega
  have rj := fun j => rv_j (16 * g.n + 24) (g.w + 2) j
  have aw : ∀ j, VG.Proof.Rsa.X86.Keys.arr g.w j = 160 + j * (4 * (g.w + 2)) := fun j => rfl
  have aW : ∀ j, VG.Proof.Rsa.X86.Keys.arr (kw (16 * g.n + 24)) j = 160 + j * (4 * (kw (16 * g.n + 24) + 2)) :=
    fun j => rfl
  have e8 : (VG.Impl.Rsa.X86.RecoverDetRt.aGm : Nat) = 8 := rfl
  have e0 : (VG.Impl.Rsa.X86.RecoverDetRt.aGx : Nat) = 0 := rfl
  have efs : fgSz = 16 := rfl
  have hfg : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) = rv (kw (16 * g.n + 24)) { arr := 4 } (g.w + 2) := rfl
  rw [aw, e8] at hm; rw [aw, e0] at hx
  simp only [seqs]
  generalize hL : 16 * g.n + 24 = len at *
  generalize hK : kw len = K at *
  -- `[7] = m`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h.ws (j := 7) (by omega))
    fun s₁ ⟨_, k₁, Z₁, K₁⟩ => ?_)
  have O₁ := keep_outside k₁
  rw [hK] at O₁ Z₁
  simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr] at O₁ Z₁
  have H₁ := h.keep K₁ (by decide) (by decide) O₁ (by omega) (by omega)
  have m₁ : val32 s₁.mem g.B (160 + 8 * (4 * (g.w + 2))) g.w = m := by rw [O₁.val32 (by omega) (by omega), hm]
  have x₁ : val32 s₁.mem g.B (160 + 0 * (4 * (g.w + 2))) g.w = x := by rw [O₁.val32 (by omega) (by omega), hx]
  refine WP.seq (WP.mono (copyOut_ok (rtNar (hL ▸ H₁.ws) up) (o := 14) (a := 8) (by decide) (by decide) (by decide))
    fun s₂ ⟨_, O₂, V₂, K₂⟩ => ?_)
  rw [ew] at O₂ V₂
  simp only [VG.Proof.Rsa.X86.Keys.num, VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
    VG.Impl.Rsa.X86.Keys.hdr] at O₂ V₂
  rw [m₁] at V₂
  have H₂ := H₁.keep K₂ (by decide) (by decide) O₂ (by omega) (by omega)
  have M₂ : val32 s₂.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by
    refine low_ext (show val32 s₂.mem g.B (160 + 7 * (4 * K + 8)) g.w = m by
      rw [show 160 + 7 * (4 * K + 8) = 160 + 14 * (4 * (g.w + 2)) by omega]; exact V₂) ?_
    rw [O₂.val32 (by omega) (by omega)]
    have := zero_sub (i := g.w) (j := 3) Z₁ (by omega)
    rw [show 160 + 7 * (4 * (K + 2)) + 4 * g.w = 160 + 7 * (4 * K + 8) + 4 * g.w by omega] at this
    exact this
  have x₂ : val32 s₂.mem g.B (160 + 0 * (4 * (g.w + 2))) g.w = x := by rw [O₂.val32 (by omega) (by omega), x₁]
  -- `[8] = x`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok H₂.ws (j := 8) (by omega))
    fun s₃ ⟨_, k₃, Z₃, K₃⟩ => ?_)
  have O₃ := keep_outside k₃
  rw [hK] at O₃ Z₃
  simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr] at O₃ Z₃
  have H₃ := H₂.keep K₃ (by decide) (by decide) O₃ (by omega) (by omega)
  have x₃ : val32 s₃.mem g.B (160 + 0 * (4 * (g.w + 2))) g.w = x := by rw [O₃.val32 (by omega) (by omega), x₂]
  have M₃ : val32 s₃.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by rw [O₃.val32 (by omega) (by omega), M₂]
  refine WP.seq (WP.mono (copyOut_ok (rtNar (hL ▸ H₃.ws) up) (o := 16) (a := 0) (by decide) (by decide) (by decide))
    fun s₄ ⟨_, O₄, V₄, K₄⟩ => ?_)
  rw [ew] at O₄ V₄
  simp only [VG.Proof.Rsa.X86.Keys.num, VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
    VG.Impl.Rsa.X86.Keys.hdr] at O₄ V₄
  rw [x₃] at V₄
  have H₄ := H₃.keep K₄ (by decide) (by decide) O₄ (by omega) (by omega)
  have X₄ : val32 s₄.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3) = x := by
    refine low_ext (show val32 s₄.mem g.B (160 + 8 * (4 * K + 8)) g.w = x by
      rw [show 160 + 8 * (4 * K + 8) = 160 + 16 * (4 * (g.w + 2)) by omega]; exact V₄) ?_
    rw [O₄.val32 (by omega) (by omega)]
    have := zero_sub (i := g.w) (j := 3) Z₃ (by omega)
    rw [show 160 + 8 * (4 * (K + 2)) + 4 * g.w = 160 + 8 * (4 * K + 8) + 4 * g.w by omega] at this
    exact this
  have M₄ : val32 s₄.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by rw [O₄.val32 (by omega) (by omega), M₃]
  have x₄ : val32 s₄.mem g.B (160 + 0 * (4 * (g.w + 2))) g.w = x := by rw [O₄.val32 (by omega) (by omega), x₃]
  -- `[9] = 0`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok H₄.ws (j := 9) (by omega))
    fun s₅ ⟨_, k₅, Z₅, K₅⟩ => ?_)
  have O₅ := keep_outside k₅
  rw [hK] at O₅ Z₅
  simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr] at O₅ Z₅
  have H₅ := H₄.keep K₅ (by decide) (by decide) O₅ (by omega) (by omega)
  have M₅ : val32 s₅.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by rw [O₅.val32 (by omega) (by omega), M₄]
  have X₅ : val32 s₅.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3) = x := by rw [O₅.val32 (by omega) (by omega), X₄]
  have x₅ : val32 s₅.mem g.B (160 + 0 * (4 * (g.w + 2))) g.w = x := by rw [O₅.val32 (by omega) (by omega), x₄]
  have rk : ∀ j, rv (kw len) { arr := j } (g.w + 2) = 160 + j * (4 * K + 8) := fun j => by rw [hK]; exact rj j
  have r4 := rk 4; have r7 := rk 7; have r8 := rk 8; have r9 := rk 9
  -- The mask of `x` even.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok H₅.ws.ws.workspace (src := 160) (by omega))
    fun s₆ ⟨c₆, K₆, m₆⟩ => ?_)
  have H₆ : Bx wid s₆ g.B g.Z len 22 (g.w + 2) := H₅.keep K₆ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₆]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have par : w32 s₅.mem g.B 160 % 2 = x % 2 := parity_low (k := g.w) (by omega) (by simpa using x₅)
  have mask : s₆.gpr .ecx = cmask (decide (x % 2 = 0)) := by
    rw [c₆, par]; by_cases e : x % 2 = 0 <;> simp [e, cmask]
  -- `[9] = m` where `x` is even.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.selIn_ok H₆ (o := { arr := 9 }) (a := { arr := 7 }) (e := 0)
    mask (by decide) (by omega) (by omega) (.inr (by omega))) fun s₇ ⟨H₇, O₇, V₇, K₇⟩ => ?_)
  simp only [Nat.add_zero] at O₇ V₇
  rw [r9] at O₇ V₇; rw [r7] at V₇
  rw [m₆] at V₇
  have M₇ : val32 s₇.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by
    rw [O₇.val32 (by omega) (by omega), m₆, M₅]
  have X₇ : val32 s₇.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3) = x := by
    rw [O₇.val32 (by omega) (by omega), m₆, X₅]
  have mlt : m < 2 ^ (32 * g.w) := hm ▸ val32_lt _ _ _ _
  have xlt : x < 2 ^ (32 * g.w) := hx ▸ val32_lt _ _ _ _
  have pw : 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 2)) := Nat.pow_le_pow_right (by decide) (by omega)
  have Y₇ : val32 s₇.mem g.B (160 + 9 * (4 * K + 8)) (g.w + 3) = if x % 2 = 0 then m else 0 := by
    have z9 : val32 s₅.mem g.B (160 + 9 * (4 * K + 8)) (g.w + 3) = 0 := by
      have := zero_sub (i := 0) (j := g.w + 3) Z₅ (by omega)
      rw [show 160 + 9 * (4 * (K + 2)) + 4 * 0 = 160 + 9 * (4 * K + 8) by omega] at this; exact this
    refine low_ext (w := g.w + 2) (j := 1) ?_ ?_
    · rw [V₇]
      by_cases e : x % 2 = 0
      · simp only [e, decide_true, ite_true]; exact val32_low (by rw [M₅]) (by omega)
      · simp only [e, decide_false, Bool.false_eq_true, ite_false]
        have := zero_sub (i := 0) (j := g.w + 2) z9 (by omega)
        simpa using this
    · rw [O₇.val32 (by omega) (by omega), m₆]
      exact zero_sub (i := g.w + 2) (j := 1) z9 (by omega)
  -- `[8] = oddInput m x`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.chainAdd_ok H₇ (o := { arr := 8 }) (a := { arr := 8 })
    (b := { arr := 9 }) (e := 1) (by decide) rfl (by omega) (by omega) (by omega) (.inl (Nat.le_refl _))
    (.inl (by omega))) fun s₈ ⟨H₈, O₈, ⟨c, _, V₈⟩, K₈⟩ => ?_)
  rw [r8] at O₈ V₈; rw [r9] at V₈
  rw [show g.w + 2 + 1 = g.w + 3 by omega] at O₈ V₈
  rw [X₇, Y₇] at V₈
  have pw3 : 2 * 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 3)) := by
    rw [show 32 * (g.w + 3) = 32 * g.w + 96 by omega, pow_add]
    exact (Nat.mul_comm 2 _).trans_le (Nat.mul_le_mul_left _ (by decide))
  have G₈ : val32 s₈.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3) = oddInput m x := by
    have hv := val32_lt s₈.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3)
    cases c
    · simpa [oddInput] using V₈
    · exfalso; simp only [Bool.toNat_true, Nat.mul_one] at V₈
      split at V₈ <;> omega
  have M₈ : val32 s₈.mem g.B (160 + 7 * (4 * K + 8)) (g.w + 3) = m := by
    rw [O₈.val32 (by omega) (by omega), M₇]
  have eP : sP = 176 := rfl
  have rF : rv (kw len) { arr := fgArr } (g.w + 2) = 160 + 4 * (4 * K + 8) := r4
  have fitF : rv (kw len) { arr := fgArr } (g.w + 2) + fgSz * (g.w + 2 + 2) ≤ 2 ^ 32 := by rw [rF, efs]; omega
  -- The rows: `f = [7]`, then `g = [8]`.
  refine WP.seq (WP.mono (scatter_ok H₈ (arr := fgArr) (sz := fgSz) (x := 0) (src := { arr := 7 }) (by decide)
    (by rw [rF, efs]; omega) (by rw [rF]; omega) (by rw [r7]; omega) (.inr (by rw [rF, r7, efs]; omega)))
    fun s₉ ⟨H₉, R₉, V₉, K₉⟩ => ?_)
  rw [r7, show g.w + 2 + 1 = g.w + 3 by omega, M₈] at V₉
  have Q₉ : Same g.B (160 + 8 * (4 * K + 8)) 4 (g.w + 3) s₈.mem s₉.mem :=
    Same.ctg_row R₉ (by decide) (.inr (by rw [rF, efs]; omega)) (.inr (by omega)) (by omega)
  have X₉ : val32 s₉.mem g.B (160 + 8 * (4 * K + 8)) (g.w + 3) = oddInput m x := by
    rw [val32_sv, Q₉.sv, ← val32_sv, G₈]
  rw [← hK]
  refine WP.mono (scatter_ok H₉ (arr := fgArr) (sz := fgSz) (x := 4) (src := { arr := 8 }) (by decide)
    (by rw [rF, efs]; omega) (by rw [rF]; omega) (by rw [r8]; omega) (.inr (by rw [rF, r8, efs]; omega)))
    fun t ⟨Ht, Rt, Vt, Kt⟩ => ⟨Ht, ?_, ?_, ?_, ?_⟩
  · rw [show g.w + 3 = g.w + 2 + 1 by omega,
      (Same.row_slot Rt (o := 4) (x := 0) (by decide) (by decide) (.inl (by decide)) (by rw [rF]; omega) fitF).sv]
    exact V₉
  · rw [Vt, r8, show g.w + 2 + 1 = g.w + 3 by omega, X₉]
  · have a₁ : Keeps wordClob s s₅ := (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
      ((K₃.mono (by decide)).trans (K₄.mono (by decide)))).trans (K₅.mono (by decide))
    have a₂ : Keeps wordClob s₅ s₈ := ((K₆.mono (by decide)).trans (K₇.mono (by decide))).trans (K₈.mono (by decide))
    exact (a₁.trans a₂).trans ((K₉.mono (by decide)).trans (Kt.mono (by decide)))
  · have U₆ : Unch g.B [] s₅.mem s₆.mem := by rw [m₆]; exact Unch.refl _ _ _
    refine (((((((((O₁.unch.trans O₂.unch).trans O₃.unch).trans O₄.unch).trans O₅.unch).trans U₆).trans
      O₇.unch).trans O₈.unch).trans (R₉.unch (by decide))).trans (Rt.unch (by decide))).cover ?_
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [rF, efs] at hw
    rw [r4]
    rcases hw with (((((((((rfl | rfl) | rfl) | rfl) | rfl) | (rfl | rfl)) | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) <;>
      dsimp only <;> omega


/-! ## The whole GCD -/

/-- The header words the fused GCD writes, from the window to the batch count. -/
abbrev gcdWSlots : List Nat :=
  [16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100]

/-- The fused GCD's writes are within the wide arrays 0, 4 to 9, 12 and 14 and the header words. -/
theorem gcdW_keep {g : Geo} {m m' : Mem} (hW : 10 ≤ g.W)
    (U : Unch g.B [(16, 88), (160, 48), (sP, 8), (160 + 4 * (4 * g.W + 8), 6 * (4 * g.W + 8)),
      (160 + 12 * (4 * g.W + 8), 4 * g.W + 8), (160 + 14 * (4 * g.W + 8), 4 * g.W + 8)] m m') :
    VG.Proof.Rsa.X86.Keys.Keep g.B g.W [0, 4, 5, 6, 7, 8, 9, 12, 14] gcdWSlots m m' := by
  intro x hx
  have each : ∀ j ∈ [0, 4, 5, 6, 7, 8, 9, 12, 14],
      ofs g.B x < VG.Proof.Rsa.X86.Keys.arr g.W j ∨
        VG.Proof.Rsa.X86.Keys.arr g.W j + VG.Proof.Rsa.X86.Keys.S g.W ≤ ofs g.B x :=
    fun j hj => hx (VG.Proof.Rsa.X86.Keys.arr g.W j, VG.Proof.Rsa.X86.Keys.S g.W) (by
      simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map]
      exact .inl ⟨j, hj, rfl⟩)
  have slots : ofs g.B x < 16 ∨ 104 ≤ ofs g.B x := by
    by_contra c
    have mem : ∀ q < 22, 16 + 4 * q ∈ gcdWSlots := by decide
    have := hx (16 + 4 * ((ofs g.B x - 16) / 4), 4) (by
      simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map]
      exact .inr ⟨_, mem _ (by omega), rfl⟩)
    simp only at this
    omega
  have h0 := each 0 (by decide); have h4 := each 4 (by decide); have h5 := each 5 (by decide)
  have h6 := each 6 (by decide); have h7 := each 7 (by decide); have h8 := each 8 (by decide)
  have h9 := each 9 (by decide); have h12 := each 12 (by decide); have h14 := each 14 (by decide)
  simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr] at h0 h4 h5 h6 h7 h8 h9 h12 h14
  have eP : sP = 176 := rfl
  apply U x
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

open VG.Impl.Rsa.X86.RecoverRt (nar) in
theorem KS.zeroWide_w {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat} {j : Nat}
    (h : KS g s0 A live AW liveW V ls s) (hj : j < VG.Impl.Rsa.X86.Recover.nArr) (hl : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.zeroWide nar j) s fun t => KS g s0 (VG.Proof.Rsa.X86.Keys.upd A j 0) (j :: live) AW liveW V ls t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h.rt hj) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  have z : VG.Proof.Rsa.X86.Keys.num t.mem g.B g.w j = 0 := by
    have e' := e
    rw [val32_succ] at e'
    exact (Nat.eq_zero_of_add_eq_zero e').1
  exact h.write_w k hj (by simp) (r.mono (by decide)) z hl (by simp)


open VG.Impl.Rsa.X86.RecoverRt (wid nar) in
open VG.Impl.Rsa.X86.RecoverDetRt (aGm aGx aG wX3 sOkDE) in
/-- The fused GCD's run, without its convergence (`GcdDone`): the frame, `[aZero] = 0`, `[aN]` kept, and
`[aG]` the reference run's `|f|` where that is below `2^(32 w)`. -/
theorem gcdFusedCore_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x : Nat}
    (h : KS g s0 A [aGm, aGx, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s)
    (hm : A aGm = m) (hx : A aGx = x) (odd : m % 2 = 1) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.gcdFused s fun t => ∃ A',
      KS g s0 A' [aG, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] t ∧
      ((rs m 0 x (2 * ((3 * g.w + 6) / 2) + 1)).f.natAbs < 2 ^ (32 * g.w) → A' aG = (rs m 0 x (2 * ((3 * g.w + 6) / 2) + 1)).f.natAbs) ∧ A' VG.Impl.Rsa.X86.Keys.aZero = 0 ∧
      A' VG.Impl.Rsa.X86.RecoverDetRt.aN = A VG.Impl.Rsa.X86.RecoverDetRt.aN := by
  have lo := h.lower; have up := h.upper
  have hr := h.rtW
  have hw : g.w = 2 * g.n + 2 := rfl
  have hW : g.W = 2 * g.w + 2 := rfl
  have eW : kw (16 * g.n + 24) = g.W := kw_wid g.n
  have ew : kw (8 * g.n + 8) = g.w := kw_nar g.n
  have hn := hr.ws.workspace.nowrap
  have mlt : m < 2 ^ (32 * g.w) := by rw [← hm, ← h.arrs aGm (by simp)]; exact val32_lt _ _ _ _
  have xlt : x < 2 ^ (32 * g.w) := by rw [← hx, ← h.arrs aGx (by simp)]; exact val32_lt _ _ _ _
  have pw2 : 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 2)) := Nat.pow_le_pow_right (by decide) (by omega)
  have lenE : ∀ a, kw (wid.toLen a) = kw (16 * g.n + 24) → kw (nar.toLen a) = kw (8 * g.n + 8) := fun a ea => by
    simp only [VG.Impl.Rsa.X86.KeyRt.Lay.toLen, VG.Impl.Rsa.X86.RecoverRt.lay, VG.Proof.Rsa.X86.KeyRt.kw,
      VG.Proof.Bignum.X86.PublicRt.wb, Spec.Rsa.modulusWords] at ea ⊢
    omega
  have code : VG.Impl.Rsa.X86.RecoverDetRt.gcdFused = seqs ([.block (slots wid ++ VG.Impl.Rsa.X86.RecoverDetRt.gN)] ++
      ([VG.Impl.Rsa.X86.KeyRt.zeroWide wid 7, VG.Impl.Rsa.X86.KeyRt.copy nar 14 aGm,
        VG.Impl.Rsa.X86.KeyRt.zeroWide wid 8, VG.Impl.Rsa.X86.KeyRt.copy nar 16 aGx,
        VG.Impl.Rsa.X86.KeyRt.zeroWide wid 9,
        .block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0)),
        selIn wid { arr := 9 } { arr := 7 } (nBytes .edi 0),
        VG.Impl.Rsa.X86.InvBatchRt.chain wid .adc { arr := 8 } { arr := 8 } { arr := 9 } (nBytes .edx 1),
        scatter wid fgArr fgSz 0 { arr := 7 }, scatter wid fgArr fgSz 4 { arr := 8 }] ++
      ([.block [.mov .eax (.imm 1), .store (sc win) .eax],
        .block (VG.Impl.Rsa.X86.KeyRt.bytesB nar .eax ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax),
          .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 6), .shift .shr .eax 1,
          .store (sc 100) .eax] : List Instr)),
        .loop (seqs [VG.Impl.Rsa.X86.RecoverDetRt.batchG true, VG.Impl.Rsa.X86.RecoverDetRt.batchG false,
          .block [.mov .esi (.mem (sc 100)), VG.Impl.Weierstrass.X86.decCounter, .store (sc 100) .esi,
            VG.Impl.Weierstrass.X86.testCounter]]) .ne,
        VG.Impl.Rsa.X86.RecoverDetRt.batchG true] ++
      ([gather wid fgArr fgSz 8 { arr := 14 }, VG.Impl.Rsa.X86.KeyRt.zeroWide wid 12,
        VG.Impl.Rsa.X86.InvBatchRt.chain wid .sbb { arr := 12 } { arr := 12 } { arr := 14 } (nBytes .edx 0),
        .block (maskAt wid { arr := 14, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
        selIn wid { arr := 12 } { arr := 14 } (nBytes .edi 0)] ++
      [VG.Impl.Rsa.X86.KeyRt.copy nar aG 24, VG.Impl.Rsa.X86.KeyRt.zeroWide nar VG.Impl.Rsa.X86.Keys.aZero])))) := rfl
  rw [code, seqs_append_iff]
  -- The slots and the rows' width.
  refine VG.Proof.Rsa.X86.InvBatchRt.slots_ok hr (by decide) fun u Hu Ku Ou => ?_
  refine WP.mono (gN_ok Hu (lenNar Hu.ws lenE) (by omega) (by rw [ew]; omega)) fun u₁ ⟨H₁, K₁, O₁⟩ => ?_
  rw [ew] at H₁
  have keepArr : ∀ j, j = aGm ∨ j = aGx → val32 u₁.mem g.B (VG.Proof.Rsa.X86.Keys.arr g.w j) g.w = A j := by
    rintro j hj
    have fit := h.ws.arr_fit (j := j) (by rcases hj with rfl | rfl <;> decide)
    simp only [VG.Proof.Rsa.X86.Keys.S] at fit
    rcases hj with rfl | rfl <;>
    · rw [O₁.val32 (by simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Impl.Rsa.X86.Keys.hdr, halfSlot]; omega) (by omega),
        Ou.val32 (by simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Impl.Rsa.X86.Keys.hdr, slotBase]; omega) (by omega)]
      exact h.arrs _ (by simp)
  have hm₁ := (keepArr aGm (.inl rfl)).trans hm
  have hx₁ := (keepArr aGx (.inr rfl)).trans hx
  -- The operands.
  rw [seqs_append_iff]
  refine WP.mono (operandsG_ok H₁ up hm₁ hx₁) fun u₂ ⟨H₂, F₂, G₂, K₂, U₂⟩ => ?_
  -- `δ = 1` and the count.
  rw [seqs_append_iff]
  refine (seqs_cons_iff _ _ _ _).2 (WP.mono (winOneN_ok H₂) fun u₃ ⟨H₃, m₃, K₃⟩ => ?_)
  refine (seqs_cons_iff _ _ _ _).2 (WP.mono (countG_ok H₃ (lenNar H₃.ws lenE) (by omega)) fun u₄ ⟨H₄, m₄, K₄⟩ => ?_)
  rw [ew] at m₄
  have hf16 := H₄.fits16
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq (16 * g.n + 24)
  have rF : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) = 160 + 4 * (4 * kw (16 * g.n + 24) + 8) :=
    rv_j (16 * g.n + 24) (g.w + 2) fgArr
  have efs : fgSz = 16 := rfl
  have e16 : win = 16 := rfl
  have O₃ : Outside g.B win 4 u₂.mem u₃.mem := by rw [m₃]; exact writeW32_outside _ _ _ (by omega)
  have O₄ : Outside g.B 100 4 u₃.mem u₄.mem := by rw [m₄]; exact writeW32_outside _ _ _ (by omega)
  have fitF : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) + fgSz * (g.w + 2 + 2) ≤ 2 ^ 32 := by
    rw [rF, efs, eW]; omega
  have far : ∀ {xo : Nat}, xo + 4 ≤ fgSz → Same g.B (rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) + fgSz + xo)
      fgSz (g.w + 2 + 1) u₂.mem u₄.mem := fun hxo =>
    (Same.apart O₃ hxo (.inr (by rw [rF, eW]; omega)) fitF).trans (Same.apart O₄ hxo (.inr (by rw [rF, eW]; omega)) fitF)
  have big : ∀ v, v < 2 ^ (32 * (g.w + 2)) → v < 2 ^ (32 * (g.w + 2)) * 2 ^ 31 := fun v hv =>
    lt_of_lt_of_le hv (Nat.le_mul_of_pos_right _ (by decide))
  have oxl : oddInput m x < 2 ^ (32 * (g.w + 2)) := by
    have := oddInput_le_two mlt xlt
    have : 2 * 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 2)) := by
      rw [show 32 * (g.w + 2) = 32 * g.w + 64 by omega, pow_add]
      exact (Nat.mul_comm 2 _).trans_le (Nat.mul_le_mul_left _ (by decide))
    omega
  have R₀ : GRun (16 * g.n + 24) (g.w + 2) g.B m 0 x 0 0 u₄ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hdr_out O₄ (.inl (by omega)) (by omega), m₃, Mem.readW_writeW_self32]; rfl
    · show sval _ _ _ _ _ = ((m : Nat) : Int)
      exact sval_nat (by rw [(far (by decide)).sv]; exact F₂) (big _ (by omega))
    · show sval _ _ _ _ _ = ((oddInput m x : Nat) : Int)
      exact sval_nat (by rw [(far (by decide)).sv]; exact G₂) (big _ oxl)
  have cnt : VG.Proof.Mont.w32 u₄.mem g.B 100 = (3 * g.w + 6) / 2 := by
    rw [m₄, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfit : rv (kw (16 * g.n + 24)) { arr := fgArr } (g.w + 2) + fgSz * (g.w + 2 + 2) < g.Z := by
    rw [rF, efs, eW]; omega
  have pc : m < 2 ^ (32 * (g.w + 2)) := by omega
  have xc : x < 2 ^ (32 * (g.w + 2)) := by omega
  -- The batches.
  refine (seqs_cons_iff _ _ _ _).2 (WP.mono (loopG_ok H₄ (by omega) (by omega) hfit odd pc xc R₀
    (by omega) (by omega) cnt) fun u₅ ⟨H₅, K₅, U₅, R₅⟩ => ?_)
  refine WP.mono (stepG_ok H₅ (by omega) (by omega) hfit (i := 0) (o := 8) (.inl ⟨rfl, rfl⟩) odd pc xc
    (by omega) R₅) fun u₆ ⟨H₆, K₆, U₆, _, R₆⟩ => ?_
  -- `|f| = gcd(m, x)` into `[12]`.
  have ox : oddInput m x ≤ m + x := by unfold oddInput; split <;> omega
  have hb : |(rs m 0 x (2 * ((3 * g.w + 6) / 2) + 1)).f| < 2 ^ (32 * (g.w + 2)) := by
    have := (dfg_bounds (iv := 0) (cap := m + x) odd (by omega) ox (2 * ((3 * g.w + 6) / 2) + 1)).2.2.1
    have p2 : 2 * 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 2)) := by
      rw [show 32 * (g.w + 2) = 32 * g.w + 64 by omega, pow_add]
      exact (Nat.mul_comm 2 _).trans_le (Nat.mul_le_mul_left _ (by decide))
    have : ((m + x : Nat) : Int) < 2 ^ (32 * (g.w + 2)) := by
      have : m + x < 2 ^ (32 * (g.w + 2)) := by omega
      exact_mod_cast this
    omega
  rw [seqs_append_iff]
  refine WP.mono (finishG_ok H₆ (by omega) (by rw [eW]; omega) R₆.f hb) fun u₇ ⟨H₇, V₇, K₇, U₇⟩ => ?_
  -- Back to the frame.
  have r12 := rv_j (16 * g.n + 24) (g.w + 2) 12
  have r14 := rv_j (16 * g.n + 24) (g.w + 2) 14
  have r4 := rv_j (16 * g.n + 24) (g.w + 2) 4
  rw [eW] at r12 r14 r4 rF
  have eP : sP = 176 := rfl
  have e52 : slotBase = 52 := rfl; have e96 : halfSlot = 96 := rfl
  have U : Unch g.B [(16, 88), (160, 48), (sP, 8), (160 + 4 * (4 * g.W + 8), 6 * (4 * g.W + 8)),
      (160 + 12 * (4 * g.W + 8), 4 * g.W + 8), (160 + 14 * (4 * g.W + 8), 4 * g.W + 8)] s.mem u₇.mem := by
    refine (((((((Ou.unch.trans O₁.unch).trans U₂).trans O₃.unch).trans O₄.unch).trans U₅).trans U₆).trans
      U₇).cover ?_
    intro w hw
    simp only [gWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [eW] at hw
    rw [r4, r12, r14, rF, efs] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> omega
  have k := gcdW_keep (by omega) U
  have rr₁ : Keeps opRegs s u₂ :=
    ((Ku.mono (by decide)).trans (K₁.mono (by decide))).trans (K₂.mono (by decide))
  have rr₂ : Keeps opRegs u₂ u₄ := (K₃.mono (by decide)).trans (K₄.mono (by decide))
  have rr₃ : Keeps opRegs u₄ u₇ :=
    ((K₅.mono (by decide)).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))
  have rr : Keeps opRegs s u₇ := (rr₁.trans rr₂).trans rr₃
  have h' : KS g s0 A [VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s :=
    h.mono (fun j hj => ⟨by simp at hj ⊢; simp [hj], rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  have aN7 := h'.arrs_W k (by decide) (by decide)
  have S₇ : KS g s0 (VG.Proof.Rsa.X86.Keys.upd A 24 (VG.Proof.Rsa.X86.Keys.num u₇.mem g.B g.w 24)) [24, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3]
      V [sOkDE] u₇ :=
    h'.core k (fun j hj => h'.wsW.arr_fit (by simp at hj; omega)) (by decide) rr
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · simp [VG.Proof.Rsa.X86.Keys.upd]
        · rw [aN7 _ (by simp)]; simp [VG.Proof.Rsa.X86.Keys.upd, VG.Impl.Rsa.X86.RecoverDetRt.aN,
            VG.Impl.Rsa.X86.Recover.aN])
      (by decide) (h'.arrsW_W k (by decide) (by decide)) (by decide) (h'.sl_keep k (by decide)) (by decide)
  -- `[aG] = [24]`, `[aZero] = 0`.
  refine (seqs_cons_iff _ _ _ _).2 (WP.mono (S₇.copy_w (o := aG) (a := 24) (by decide) (by simp) (by decide)
    (by decide)) fun u₈ ⟨S₈, _, _⟩ => ?_)
  refine WP.mono (KS.zeroWide_w S₈ (by decide) (by decide)) fun t St => ⟨_, St.mono (fun j hj => ⟨by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩), fun hlt => ?_, ?_, ?_⟩
  · have g24 : VG.Proof.Rsa.X86.Keys.num u₇.mem g.B g.w 24 = (rs m 0 x (2 * ((3 * g.w + 6) / 2) + 1)).f.natAbs := by
      show val32 u₇.mem g.B (VG.Proof.Rsa.X86.Keys.arr g.w 24) g.w = _
      rw [show VG.Proof.Rsa.X86.Keys.arr g.w 24 = rv (kw (16 * g.n + 24)) { arr := 12 } (g.w + 2) by
        rw [eW, r12]; simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]; omega]
      have p1 : 2 ^ (32 * g.w) ≤ 2 ^ (32 * (g.w + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      exact val32_low (val32_low (k := g.w + 1) V₇ (by omega)) hlt
    simp [VG.Proof.Rsa.X86.Keys.upd, aG, VG.Impl.Rsa.X86.Keys.aZero, g24]
  all_goals simp [VG.Proof.Rsa.X86.Keys.upd, aG, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN,
    VG.Impl.Rsa.X86.Recover.aN]

open VG.Impl.Rsa.X86.RecoverDetRt (aGm aGx aG wX3 sOkDE) in
/-- The fused GCD: `[aG] = gcd(m, x)` for an odd `m` in `[aGm]` and `x` in `[aGx]`, `[aZero] = 0`, the
rows of `w + 2` words. -/
theorem gcdFused_ok [GcdDone] {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x : Nat}
    (h : KS g s0 A [aGm, aGx, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s)
    (hm : A aGm = m) (hx : A aGx = x) (odd : m % 2 = 1) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.gcdFused s fun t => ∃ A',
      KS g s0 A' [aG, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] t ∧
      A' aG = Nat.gcd m x ∧ A' VG.Impl.Rsa.X86.Keys.aZero = 0 ∧
      A' VG.Impl.Rsa.X86.RecoverDetRt.aN = A VG.Impl.Rsa.X86.RecoverDetRt.aN := by
  have mlt : m < 2 ^ (32 * g.w) := by rw [← hm, ← h.arrs aGm (by simp)]; exact val32_lt _ _ _ _
  have xlt : x < 2 ^ (32 * g.w) := by rw [← hx, ← h.arrs aGx (by simp)]; exact val32_lt _ _ _ _
  have done := GcdDone.done (iv := 0) (n := g.w) (j := 2 * ((3 * g.w + 6) / 2) + 1) odd mlt xlt (by omega)
  have gle : Nat.gcd m x ≤ m := Nat.gcd_le_left x (by omega)
  exact WP.mono (gcdFusedCore_ok h hm hx odd) fun t ⟨A', h', v, z, n'⟩ =>
    ⟨A', h', by rw [v (by rw [done.2]; omega), done.2], z, n'⟩

end VG.Proof.Rsa.X86.Recover.G
