module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the halvings

`twos_ok`: `64 v` steps of `RecoverDet.twoStep` from `(n - 1, X mod 2^(64 v), X)`,
`u` and `x` narrow (arrays 2 and 3) and `X` wide (array 6).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- A word's parity is its number's. -/
theorem par_word {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) : (word m B e).toNat % 2 = wv m B e w % 2 := by
  rw [wv_low hw]; omega

/-- `twosFlags`: `x1` the mask of `u` even, `x2` that of `x` and `u` even. -/
theorem twosFlags_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block twosFlags) s fun t =>
      (t.gpr .x1 = mask (decide (wv s.mem B (slot w nU) w % 2 = 0)) ∧
        t.gpr .x2 = mask (decide (wv s.mem B (slot w nU) w % 2 = 0) && decide (wv s.mem B (slot w nXn) w % 2 = 0)) ∧
        t.mem = s.mem) ∧ Keep [.x1, .x2, .x3, .x4, .x11, .x12, .x16] s t := by
  have hw1 : 1 ≤ w := by have := h.w1; omega
  have hn := h.scr.nowrap
  have sU := h.sl (j := nU) (by decide)
  have sX := h.sl (j := nXn) (by decide)
  unfold twosFlags
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok nU .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun t₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x3, .x4] (Q := fun t => t.gpr .x1 = mask (decide ((word s.mem B (slot w nU)).toNat % 2 = 0)) ∧
      t.gpr .x4 = BitVec.ofNat 64 1 ∧ t.mem = t₂.mem)
    (by brun [h16, hs₂.ld (d := slot w nU) (by omega), m₂, m₁, low_sub_one]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h1, h4, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok nXn .x16 (((k₁.trans k₂).trans k₃).gpr .x0 (by decide) |>.trans h.x0)
    ((k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11))) fun t₄ ⟨⟨h16₄, m₄, _⟩, k₄⟩ => ?_
  have hs₄ := hs₂.congr (k₃.trans k₄).wr
  refine WP.mono (WP.keep [.x2, .x3] (Q := fun t => t.gpr .x2 = mask (decide ((word s.mem B (slot w nXn)).toNat % 2 = 0)) &&&
      mask (decide ((word s.mem B (slot w nU)).toNat % 2 = 0)) ∧ t.mem = t₄.mem)
    (by
      have h4' : t₄.gpr .x4 = BitVec.ofNat 64 1 := (k₄.gpr .x4 (by decide)).trans h4
      have h1' : t₄.gpr .x1 = _ := (k₄.gpr .x1 (by decide)).trans h1
      brun [h16₄, hs₄.ld (d := slot w nXn) (by omega), m₄, m₃, m₂, m₁, h4', h1']
      exact congrArg (fun z => z &&& _) (low_sub_one (word s.mem B (slot w nXn)))) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h2, mt⟩, k₅⟩ => ?_
  refine ⟨⟨?_, ?_, by rw [mt, m₄, m₃, m₂, m₁]⟩, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [(k₅.gpr .x1 (by decide)).trans ((k₄.gpr .x1 (by decide)).trans h1), par_word hw1]
  · rw [h2, mask_and', par_word hw1, par_word hw1, Bool.and_comm]

/-- `mov x15 r`. -/
theorem mov15_ok (s : State) {r : Reg} (hr : r = .x1 ∨ r = .x2) :
    WP isa (.block [mov .x15 r]) s fun t => (t.gpr .x15 = s.gpr r ∧ t.mem = s.mem) ∧ Keep [.x15] s t := by
  rcases hr with rfl | rfl <;> exact WP.keep [.x15] (by brun) (by decide) (by decide) (by decide +kernel)

/-- After `j` halvings. -/
structure TwI (I : RpIn) (m₀ : Mem) (c : Bool) (N : Nat) (st : Nat × Nat × Nat) (j : Nat) (t : State) : Prop where
  g : G I m₀ (vk I.k) c t
  val : (wv t.mem I.B (slot (vk I.k) nU) (vk I.k), wv t.mem I.B (slot (vk I.k) nXn) (vk I.k),
    wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k)) = (twoStep (64 * Wk I.k))^[j] st
  zU : word t.mem I.B (slot (vk I.k) nU + 8 * vk I.k) = 0
  zX : word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  n : wv t.mem I.B (slot (vk I.k) 0) (vk I.k) = N
  one : wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1

theorem twoStep_val {b : Nat} (u x : Nat) {X : Nat} (hX : X < 2 ^ b) : twoStep b (u, x, X) =
    ((if decide (u % 2 = 0) then u / 2 else u), (if (decide (u % 2 = 0) && decide (x % 2 = 0)) then x / 2 else x),
      ((if (decide (u % 2 = 0) && decide (x % 2 = 0)) then X else 0) + X) % 2 ^ b) := by
  unfold twoStep
  by_cases a : u % 2 = 0 <;> by_cases b' : x % 2 = 0 <;> simp [a, b', Nat.mod_eq_of_lt hX, Nat.two_mul]

/-- What a halving step keeps: words of `u` and `x` above them, `n` and one. -/
theorem twos_keep {B : Addr} {v : Nat} {m m' : Mem} (hv : 1 ≤ v) (hb : slot v 32 ≤ 2 ^ 64)
    (F : Frm B (hdrW ++ [(slot v nT, 8 * v), (slot v nU, 8 * v), (slot v nXn, 8 * v), (slot (2 * v + 2) wT, 8 * (2 * v + 2)),
      (slot (2 * v + 2) wX, 8 * (2 * v + 2))]) m m') :
    word m' B (slot v nU + 8 * v) = word m B (slot v nU + 8 * v) ∧
    word m' B (slot v nXn + 8 * v) = word m B (slot v nXn + 8 * v) ∧
    wv m' B (slot v 0) v = wv m B (slot v 0) v ∧ wv m' B (slot v nOne) (v + 2) = wv m B (slot v nOne) (v + 2) := by
  have s32 := slot_lt (w := v) (show nOne < 32 by decide)
  have s3 := slot_lt (w := v) (show nXn < 32 by decide)
  have s2 := slot_lt (w := v) (show nU < 32 by decide)
  have s0 := slot_lt (w := v) (show 0 < 32 by decide)
  refine ⟨Frm.hdr_word F (by have := slot_ge v nU; omega) (by omega) ?_, Frm.hdr_word F (by have := slot_ge v nXn; omega)
    (by omega) ?_, Frm.hdr_wv F (slot_ge _ _) (by omega) ?_, Frm.hdr_wv F (slot_ge _ _) (by omega) ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact wd_sep (by decide) (by omega) (by omega)
      | exact wdw_sep (by decide) (by decide) (by omega) (by omega)
      | exact rd_sep (by decide) (by omega) (by omega)
      | exact nw_sep (by decide) (by decide) (by omega) (by omega)
      | exact .inr (by omega)

theorem twosStep_ok {I : RpIn} {m₀ : Mem} {c : Bool} {N : Nat} {st : Nat × Nat × Nat} {j : Nat} {t : State}
    (L : RpLens I) (hI : TwI I m₀ c N st j t) :
    WP isa twosBody t fun t' => TwI I m₀ c N st (j + 1) t' ∧ t'.gpr .x6 = t.gpr .x6 - BitVec.ofNat 64 1 := by
  have g := hI.g
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have vlt : vk I.k < 2 ^ 31 := by have := L.k2; simp only [vk]; omega
  have b0 : slot (vk I.k) 0 + 8 * (vk I.k + 2) ≤ 2 ^ 64 := g.bndv L (by decide) (Nat.le_refl _)
  have b1 : slot (vk I.k) nOne + 8 * (vk I.k + 2) ≤ 2 ^ 64 := g.bndv L (by decide) (Nat.le_refl _)
  have b2 : slot (vk I.k) nU + 8 * (vk I.k + 2) ≤ 2 ^ 64 := g.bndv L (by decide) (Nat.le_refl _)
  have b3 : slot (vk I.k) nXn + 8 * (vk I.k + 2) ≤ 2 ^ 64 := g.bndv L (by decide) (Nat.le_refl _)
  have bX : slot (Wk I.k) wX + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := g.bndW L (by decide) (Nat.le_refl _)
  have bX' : slot (2 * vk I.k + 2) wX + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bX
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := g.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _); have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  generalize hU : wv t.mem I.B (slot (vk I.k) nU) (vk I.k) = U
  generalize hXn : wv t.mem I.B (slot (vk I.k) nXn) (vk I.k) = Xn
  generalize hXW : wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k) = XW
  have hval : (U, Xn, XW) = (twoStep (64 * Wk I.k))^[j] st := by rw [← hU, ← hXn, ← hXW]; exact hI.val
  have hXlt : XW < 2 ^ (64 * Wk I.k) := by rw [← hXW]; exact wv_lt _ _ _ _
  unfold twosBody
  simp only [seqs]
  -- The flags.
  refine WP.seq (WP.mono (twosFlags_ok g.ws) fun t₁ ⟨⟨h1, h2, m₁⟩, k₁⟩ => ?_)
  rw [hU] at h1
  rw [hU, hXn] at h2
  have g₁ := g.same m₁ k₁ (by decide)
  -- `u` halved if even.
  refine WP.seq (WP.mono (halfA_ok g₁.ws (o := nT) (a := nU) (by decide) (by decide) (by rw [m₁]; exact hI.zU))
    fun t₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (by omega) o₂ k₂ (by decide)
  rw [m₁, hU] at v₂
  refine WP.seq (WP.mono (mov15_ok t₂ (.inl rfl)) fun t₃ ⟨⟨h15, m₃⟩, k₃⟩ => ?_)
  have g₃ := g₂.same m₃ k₃ (by decide)
  rw [k₂.gpr .x1 (by decide), h1] at h15
  have uT₃ : wv t₃.mem I.B (slot (vk I.k) nU) (vk I.k) = U := by
    rw [m₃, o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hU]
  refine WP.seq (WP.mono (selA_ok g₃.ws (o := nU) (a := nT) (by decide) (by decide) (by decide) h15)
    fun t₄ ⟨v₄, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  rw [uT₃, m₃, v₂] at v₄
  -- `x` halved if both are even.
  have zX₄ : word t₄.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := by
    rw [o₄.word (wd_sep (by decide) (by omega) (by omega)) (by omega), m₃,
      o₂.word (wd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hI.zX]
  have xT₄ : wv t₄.mem I.B (slot (vk I.k) nXn) (vk I.k) = Xn := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₃,
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hXn]
  refine WP.seq (WP.mono (halfA_ok g₄.ws (o := nT) (a := nXn) (by decide) (by decide) zX₄)
    fun t₅ ⟨v₅, o₅, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (by omega) o₅ k₅ (by decide)
  rw [xT₄] at v₅
  refine WP.seq (WP.mono (mov15_ok t₅ (.inr rfl)) fun t₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ?_)
  have g₆ := g₅.same m₆ k₆ (by decide)
  rw [k₅.gpr .x2 (by decide), k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), h2] at h15₆
  have xT₆ : wv t₆.mem I.B (slot (vk I.k) nXn) (vk I.k) = Xn := by
    rw [m₆, o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), xT₄]
  refine WP.seq (WP.mono (selA_ok g₆.ws (o := nXn) (a := nT) (by decide) (by decide) (by decide) h15₆)
    fun t₇ ⟨v₇, o₇, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (by omega) o₇ k₇ (by decide)
  rw [xT₆, m₆, v₅] at v₇
  -- `X` doubled if both are even.
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (g₇.setWid_ok L) fun t₈ ⟨g₈, f₈, k₈⟩ => ?_
  refine WP.mono (mov15_ok t₈ (.inr rfl)) fun t₉ ⟨⟨h15₉, m₉⟩, k₉⟩ => ?_
  have g₉ := g₈.same m₉ k₉ (by decide)
  rw [k₈.gpr .x2 (by decide), k₇.gpr .x2 (by decide), k₆.gpr .x2 (by decide), k₅.gpr .x2 (by decide),
    k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), h2] at h15₉
  have XT₉ : wv t₉.mem I.B (slot (Wk I.k) wX) (Wk I.k) = XW := by
    rw [m₉, Frm.hdrW_wv f₈ (slot_ge _ _) (by omega),
      o₇.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      m₆, o₅.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega), m₃,
      o₂.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega), m₁, hXW]
  refine WP.seq (WP.mono (addA_ok g₉.ws (o := wT) (a := wX) (b := wX) (by decide) (by decide) (by decide)
    (by decide) (by decide) h15₉) fun t₁₀ ⟨v₁₀, _, o₁₀, k₁₀⟩ => ?_)
  have g₁₀ := g₉.out (by decide) (by omega) o₁₀ k₁₀ (by decide)
  rw [XT₉] at v₁₀
  refine WP.seq (WP.mono (copyA_ok g₁₀.ws (o := wX) (a := wT) (by decide) (by decide) (by decide))
    fun t₁₁ ⟨v₁₁, o₁₁, _, _, k₁₁⟩ => ?_)
  have g₁₁ := g₁₀.out (by decide) (by omega) o₁₁ k₁₁ (by decide)
  rw [v₁₀] at v₁₁
  rw [WP.block_append_iff]
  refine WP.mono (g₁₁.setNar_ok L) fun t₁₂ ⟨g₁₂, f₁₂, k₁₂⟩ => ?_
  refine WP.mono (dec_ok t₁₂ .x6) fun t' ⟨⟨h6, m', _⟩, k₁₃⟩ => ?_
  have F : Frm I.B (hdrW ++ [(slot (vk I.k) nT, 8 * vk I.k), (slot (vk I.k) nU, 8 * vk I.k),
      (slot (vk I.k) nXn, 8 * vk I.k), (slot (Wk I.k) wT, 8 * Wk I.k), (slot (Wk I.k) wX, 8 * Wk I.k)]) t.mem t'.mem := by
    intro x hx
    have hh := fun r (hr : r ∈ hdrW) => hx r (List.mem_append_left _ hr)
    have a := hx (slot (vk I.k) nT, 8 * vk I.k) (by simp)
    have b := hx (slot (vk I.k) nU, 8 * vk I.k) (by simp)
    have c' := hx (slot (vk I.k) nXn, 8 * vk I.k) (by simp)
    have d := hx (slot (Wk I.k) wT, 8 * Wk I.k) (by simp)
    have e := hx (slot (Wk I.k) wX, 8 * Wk I.k) (by simp)
    dsimp only at a b c' d e
    rw [m', f₁₂ x hh, o₁₁ x e, o₁₀ x d, m₉, f₈ x hh, o₇ x c', m₆, o₅ x a, o₄ x b, m₃, o₂ x a, m₁]
  have k' := (((((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans k₉).trans
    k₁₀).trans k₁₁).trans k₁₂).trans k₁₃
  refine ⟨⟨g₁₂.same m' k₁₃ (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Function.iterate_succ_apply', ← hval, twoStep_val _ _ hXlt, m', Frm.hdrW_wv f₁₂ (slot_ge _ _) (by omega),
      Frm.hdrW_wv f₁₂ (slot_ge _ _) (by omega), Frm.hdrW_wv f₁₂ (slot_ge _ _) (by omega), v₁₁]
    rw [o₁₁.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₁₀.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), m₉,
      Frm.hdrW_wv f₈ (slot_ge _ _) (by omega), o₇.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₆,
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₄,
      o₁₁.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₁₀.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), m₉,
      Frm.hdrW_wv f₈ (slot_ge _ _) (by omega), v₇]
  · rw [(twos_keep hv1 hb32 F).1, hI.zU]
  · rw [(twos_keep hv1 hb32 F).2.1, hI.zX]
  · rw [(twos_keep hv1 hb32 F).2.2.1, hI.n]
  · rw [(twos_keep hv1 hb32 F).2.2.2, hI.one]
  · rw [h6, k₁₂.gpr .x6 (by decide), k₁₁.gpr .x6 (by decide), k₁₀.gpr .x6 (by decide), k₉.gpr .x6 (by decide),
      k₈.gpr .x6 (by decide), k₇.gpr .x6 (by decide), k₆.gpr .x6 (by decide), k₅.gpr .x6 (by decide),
      k₄.gpr .x6 (by decide), k₃.gpr .x6 (by decide), k₂.gpr .x6 (by decide), k₁.gpr .x6 (by decide)]


/-- `countN`: `x6 := 64 w`. -/
theorem countN_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block countN) s fun t => (t.gpr .x6 = BitVec.ofNat 64 (64 * w) ∧ t.mem = s.mem) ∧
      Keep [.x6, .x11, .x12] s t := by
  have hw2 := h.w2
  unfold countN
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * w) ∧ t.mem = t₁.mem)
    (by brun [h12, shl_ofNat (show w * 2 ^ 6 < 2 ^ 64 by omega)]; congr 1; omega) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨h6, m₂⟩, k₂⟩ => ⟨⟨h6, m₂.trans m₁⟩, (k₁.trans k₂).mono (by decide)⟩

/-- The halvings' start: `u = n - 1`, `x = X mod 2^(64 v)`, one, and `x6 := 64 v`. -/
theorem twosInit_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {N X : Nat} (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hN1 : 1 ≤ N)
    (hX : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) = X) :
    WP isa (seqs (([.block setNar] : List (Prog isa)) ++ oneA nOne ++ ([zeroA nU, subA nU Public.aN nOne, zeroA nXn,
      copyA nXn (2 * wX), .block countN] : List (Prog isa)))) s fun t => TwI I m₀ c N (N - 1, X % 2 ^ (64 * vk I.k), X) 0 t ∧
        t.gpr .x6 = BitVec.ofNat 64 (64 * vk I.k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  have s0 := slot_lt (w := vk I.k) (show 0 < 32 by decide)
  have s1 := slot_lt (w := vk I.k) (show nOne < 32 by decide)
  have s2 := slot_lt (w := vk I.k) (show nU < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nXn < 32 by decide)
  have s12 := slot_lt (w := vk I.k) (show 2 * wX + 1 < 32 by decide)
  have e12 : slot (Wk I.k) wX = slot (vk I.k) (2 * wX) := slot_wide _ _
  have sW6 : slot (vk I.k) (2 * wX) + 8 * Wk I.k ≤ 2 ^ 64 := by
    have := h.bndW L (j := wX) (k := Wk I.k) (by decide) (by omega); rw [e12] at this; exact this
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [oneA]) (WP.mono (h.setNar_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  have hN₁ : wv s₁.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by rw [Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hN]
  have hX₁ : wv s₁.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [Frm.hdrW_wv f₁ (slot_ge _ _) sW6, ← e12, hX]
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (oneA_ok g₁ (j := nOne) (by decide))
    fun s₂ ⟨g₂, v₂, o₂, k₂⟩ => ?_)
  have hN₂ : wv s₂.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hN₁]
  have hX₂ : wv s₂.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [o₂.wv (.inr (by have := slot_lt (w := vk I.k) (show nOne < 2 * wX by decide); omega))
      sW6, hX₁]
  have one₂ : wv s₂.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [v₂]; exact Nat.one_lt_two_pow (by omega)), v₂]
  simp only [seqs]
  -- `u = n - 1`.
  refine WP.seq (WP.mono (zeroA_ok g₂.ws (j := nU) (by decide)) fun s₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (subA_ok g₃.ws (o := nU) (a := Public.aN) (b := nOne) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨v₄, _, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  rw [show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl] at v₄
  rw [show wv s₃.mem I.B (slot (vk I.k) 0) (vk I.k) = N by
      rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]; exact hN₂,
    show wv s₃.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 by
      rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]; exact one₂] at v₄
  have hu : wv s₄.mem I.B (slot (vk I.k) nU) (vk I.k) = N - 1 := by
    simp only [decide_eq_true hN1, Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at v₄; omega
  -- `x`.
  refine WP.seq (WP.mono (zeroA_ok g₄.ws (j := nXn) (by decide)) fun s₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (copyA_ok g₅.ws (o := nXn) (a := 2 * wX) (by decide) (by decide) (by decide))
    fun s₆ ⟨v₆, o₆, _, _, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (by omega) o₆ k₆ (by decide)
  have hb12 : slot (vk I.k) (2 * wX) + 8 * (vk I.k + 2) ≤ 2 ^ 64 := by omega
  have x₅ : wv s₅.mem I.B (slot (vk I.k) (2 * wX)) (Wk I.k) = X := by
    rw [o₅.wv (.inr (by have := slot_lt (w := vk I.k) (show nXn < 2 * wX by decide); omega)) sW6,
      o₄.wv (.inr (by have := slot_lt (w := vk I.k) (show nU < 2 * wX by decide); omega)) sW6,
      o₃.wv (.inr (by have := slot_lt (w := vk I.k) (show nU < 2 * wX by decide); omega)) sW6, hX₂]
  refine WP.mono (countN_ok g₆.ws) fun t ⟨⟨h6, mt⟩, k₇⟩ => ⟨⟨g₆.same mt k₇ (by decide), ?_, ?_, ?_, ?_, ?_⟩, h6⟩
  · rw [Function.iterate_zero_apply, Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [mt, o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
        o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hu]
    · rw [mt, v₆, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k by omega), x₅]
    · rw [mt, e12, o₆.wv (.inr (by have := slot_lt (w := vk I.k) (show nXn < 2 * wX by decide); omega)) sW6, x₅]
  · rw [mt, o₆.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.word (wd_sep (by decide) (by omega) (by omega)) (by omega), o₄.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₃ (vk I.k) (by omega)
  · rw [mt, o₆.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₅ (vk I.k) (by omega)
  · rw [mt, o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hN₂]
  · rw [mt, o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₂]

/-- `twos`: `64 v` halvings. -/
theorem twos_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {N X : Nat} (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hN1 : 1 ≤ N)
    (hX : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) = X) :
    WP isa twos s (TwI I m₀ c N (N - 1, X % 2 ^ (64 * vk I.k), X) (64 * vk I.k)) := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hv2 : vk I.k ≤ 200 := by have := L.k2; simp only [vk]; omega
  have e : twos = seqs (([.block setNar] ++ oneA nOne ++ [zeroA nU, subA nU Public.aN nOne, zeroA nXn,
      copyA nXn (2 * wX), .block countN]) ++ [.loop twosBody (.nonzero .x .x6)]) := by
    simp only [twos, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (twosInit_ok h L hN hN1 hX) fun t ⟨hI, h6⟩ => ?_)
  exact wp_countdown (N := 64 * vk I.k) (by omega) (by omega) _ (fun i _ t' hI' _ => twosStep_ok L hI') hI h6

end VG.Proof.Rsa.AArch64.Rd
