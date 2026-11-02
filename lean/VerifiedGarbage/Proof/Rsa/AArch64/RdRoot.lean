module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdProd
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the square root

`sqrt_ok`: `32 W` steps of `RecoverDet.sqrtStep` from `(X, 0, 0)`, the
radicand `X` wide (array 7), the remainder (narrow array 2) and the root (4)
narrow, and the remainder zero and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

theorem dbl_mod {a c P : Nat} (hP : 2 ∣ P) (hc : c ≤ 1) : (2 * a + c) % P = 2 * a % P + c := by
  obtain ⟨Q, rfl⟩ := hP
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  have h1 : 2 * a % (2 * Q) = 2 * (a % Q) := Nat.mul_mod_mul_left 2 a Q
  have h2 : a % Q < Q := Nat.mod_lt _ hQ
  rw [Nat.add_mod, h1, Nat.mod_eq_of_lt (show c < 2 * Q by omega), Nat.mod_eq_of_lt (by omega)]

theorem two_pow_even {b : Nat} (hb : 1 ≤ b) : 2 ∣ 2 ^ b := ⟨2 ^ (b - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

theorem top_bit {x b : Nat} (hx : x < 2 ^ b) : (2 * x + false.toNat) / 2 ^ b = (decide (2 ^ b ≤ 2 * x)).toNat := by
  by_cases h : 2 ^ b ≤ 2 * x
  · simp only [h, decide_true, Bool.toNat_true, Bool.toNat_false, Nat.add_zero]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · simp only [h, decide_false, Bool.toNat_false, Nat.add_zero]
    exact Nat.div_eq_of_lt (by omega)

/-- The step as the code computes it. -/
theorem sqrtStep_code {nb wb : Nat} (hnb : 1 ≤ nb) {x r y : Nat} (hx : x < 2 ^ wb) :
    sqrtStep nb wb (x, r, y) = ((2 * ((2 * x + false.toNat) % 2 ^ wb) + false.toNat) % 2 ^ wb,
      (if decide ((2 * ((2 * y + false.toNat) % 2 ^ nb) + true.toNat) % 2 ^ nb ≤
          (2 * ((2 * r + (decide (2 ^ wb ≤ 2 * x)).toNat) % 2 ^ nb) +
            (decide (2 ^ wb ≤ 2 * ((2 * x + false.toNat) % 2 ^ wb))).toNat) % 2 ^ nb) then
        wsub nb ((2 * ((2 * r + (decide (2 ^ wb ≤ 2 * x)).toNat) % 2 ^ nb) +
            (decide (2 ^ wb ≤ 2 * ((2 * x + false.toNat) % 2 ^ wb))).toNat) % 2 ^ nb)
          ((2 * ((2 * y + false.toNat) % 2 ^ nb) + true.toNat) % 2 ^ nb)
      else (2 * ((2 * r + (decide (2 ^ wb ≤ 2 * x)).toNat) % 2 ^ nb) +
            (decide (2 ^ wb ≤ 2 * ((2 * x + false.toNat) % 2 ^ wb))).toNat) % 2 ^ nb),
      (2 * y + (decide ((2 * ((2 * y + false.toNat) % 2 ^ nb) + true.toNat) % 2 ^ nb ≤
          (2 * ((2 * r + (decide (2 ^ wb ≤ 2 * x)).toNat) % 2 ^ nb) +
            (decide (2 ^ wb ≤ 2 * ((2 * x + false.toNat) % 2 ^ wb))).toNat) % 2 ^ nb)).toNat) % 2 ^ nb) := by
  have ev := two_pow_even hnb
  generalize hhi : decide (2 ^ wb ≤ 2 * x) = hi
  generalize hx1 : (2 * x + false.toNat) % 2 ^ wb = x1
  generalize hlo : decide (2 ^ wb ≤ 2 * x1) = lo
  have x1lt : x1 < 2 ^ wb := by rw [← hx1]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have eA : 2 * x / 2 ^ wb = hi.toNat := by rw [← hhi, ← top_bit hx]; simp
  have eB : 2 * x % 2 ^ wb = x1 := by rw [← hx1]; simp
  have eC : 2 * x1 / 2 ^ wb = lo.toNat := by rw [← hlo, ← top_bit x1lt]; simp
  have hile : hi.toNat ≤ 1 := by cases hi <;> decide
  have lole : lo.toNat ≤ 1 := by cases lo <;> decide
  have eR : (2 * ((2 * r + hi.toNat) % 2 ^ nb) + lo.toNat) % 2 ^ nb = 2 * (2 * r % 2 ^ nb + hi.toNat) % 2 ^ nb + lo.toNat := by
    rw [dbl_mod ev hile, dbl_mod ev lole]
  have eT : (2 * ((2 * y + false.toNat) % 2 ^ nb) + true.toNat) % 2 ^ nb = 2 * (2 * y % 2 ^ nb) % 2 ^ nb + 1 := by
    rw [show (2 * y + false.toNat) = 2 * y by simp, dbl_mod ev (by decide)]; rfl
  rw [eR, eT]
  unfold sqrtStep
  simp only [eA, eB, eC]
  have rlt : 2 * (2 * r % 2 ^ nb + hi.toNat) % 2 ^ nb + lo.toNat < 2 ^ nb := by
    rw [← eR]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  by_cases c : 2 * (2 * y % 2 ^ nb) % 2 ^ nb + 1 ≤ 2 * (2 * r % 2 ^ nb + hi.toNat) % 2 ^ nb + lo.toNat
  · have c' : ¬(2 * (2 * r % 2 ^ nb + hi.toNat) % 2 ^ nb + lo.toNat < 2 * (2 * y % 2 ^ nb) % 2 ^ nb + 1) := by omega
    simp only [c', c, decide_true, ↓reduceIte, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, Prod.mk.injEq, true_and]
    exact ⟨wsub_of_le rlt c |>.symm, (dbl_mod ev (by decide)).symm⟩
  · have c' : 2 * (2 * r % 2 ^ nb + hi.toNat) % 2 ^ nb + lo.toNat < 2 * (2 * y % 2 ^ nb) % 2 ^ nb + 1 := by omega
    simp only [c', c, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]

/-- The ranges the square root writes. -/
abbrev rootRanges (v : Nat) : List (Nat × Nat) :=
  hdrW ++ [(slot (2 * v + 2) wX4, 8 * (2 * v + 2)), (slot v nRm, 8 * v), (slot v nTy, 8 * v), (slot v nDf, 8 * v),
    (slot v nY, 8 * v)]

/-- After `j` steps of the square root from `s₀`. -/
structure SI (I : RpIn) (m₀ : Mem) (c : Bool) (s₀ : State) (st : Nat × Nat × Nat) (j : Nat) (u : State) : Prop where
  g : G I m₀ (vk I.k) c u
  val : (wv u.mem I.B (slot (Wk I.k) wX4) (Wk I.k), wv u.mem I.B (slot (vk I.k) nRm) (vk I.k),
    wv u.mem I.B (slot (vk I.k) nY) (vk I.k)) = (sqrtStep (64 * vk I.k) (64 * Wk I.k))^[j] st
  frm : Frm I.B (rootRanges (vk I.k)) s₀.mem u.mem

theorem sqrtStepCode_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s₀ : State} {st : Nat × Nat × Nat} {j : Nat} {u : State}
    (L : RpLens I) (hI : SI I m₀ c s₀ st j u) :
    WP isa sqrtBody u fun u' => SI I m₀ c s₀ st (j + 1) u' ∧ u'.gpr .x6 = u.gpr .x6 - BitVec.ofNat 64 1 := by
  have g := hI.g
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 := hb32_of g L
  have s2 := slot_lt (w := vk I.k) (show nRm < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nDf < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show nY < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show nTy < 32 by decide)
  have bX : slot (Wk I.k) wX4 + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := g.bndW L (by decide) (Nat.le_refl _)
  have bX' : slot (2 * vk I.k + 2) wX4 + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bX
  generalize hX : wv u.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = X
  generalize hR : wv u.mem I.B (slot (vk I.k) nRm) (vk I.k) = R
  generalize hY : wv u.mem I.B (slot (vk I.k) nY) (vk I.k) = Y
  have hval : (X, R, Y) = (sqrtStep (64 * vk I.k) (64 * Wk I.k))^[j] st := by rw [← hX, ← hR, ← hY]; exact hI.val
  have hXlt : X < 2 ^ (64 * Wk I.k) := by rw [← hX]; exact wv_lt _ _ _ _
  unfold sqrtBody
  simp only [seqs]
  -- The radicand's two bits.
  refine WP.seq (WP.mono (g.setWid_ok L) fun u₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (dblc_ok g₁.ws (a := wX4) (by decide) (b := false) (fun t h7 _ => c0_ok t h7) (r := .x1) (.inl rfl))
    fun u₂ ⟨v₂, h1, _, o₂, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (by omega) o₂ k₂ (by decide)
  rw [Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hX] at v₂ h1
  refine WP.seq (WP.mono (dblc_ok g₂.ws (a := wX4) (by decide) (b := false) (fun t h7 _ => c0_ok t h7) (r := .x2) (.inr rfl))
    fun u₃ ⟨v₃, h2, _, o₃, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (by omega) o₃ k₃ (by decide)
  rw [v₂] at v₃ h2
  refine WP.seq (WP.mono (g₃.setNar_ok L) fun u₄ ⟨g₄, f₄, k₄⟩ => ?_)
  have x1lt : (2 * X + false.toNat) % 2 ^ (64 * Wk I.k) < 2 ^ (64 * Wk I.k) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [top_bit hXlt] at h1
  rw [top_bit x1lt] at h2
  have R₄ : wv u₄.mem I.B (slot (vk I.k) nRm) (vk I.k) = R := by
    rw [Frm.hdrW_wv f₄ (slot_ge _ _) (by omega), o₃.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hR]
  have Y₄ : wv u₄.mem I.B (slot (vk I.k) nY) (vk I.k) = Y := by
    rw [Frm.hdrW_wv f₄ (slot_ge _ _) (by omega), o₃.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hY]
  -- The remainder takes the two bits.
  refine WP.seq (WP.mono (dbl_ok g₄.ws (a := nRm) (by decide) (b := decide (2 ^ (64 * Wk I.k) ≤ 2 * X))
    (fun t h7 hk => cOf_ok t (.inl rfl) (by rw [hk .x1 (by decide), k₄.gpr .x1 (by decide), k₃.gpr .x1 (by decide), h1])))
    fun u₅ ⟨v₅, _, o₅, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (by omega) o₅ k₅ (by decide)
  rw [R₄] at v₅
  refine WP.seq (WP.mono (dbl_ok g₅.ws (a := nRm) (by decide)
    (b := decide (2 ^ (64 * Wk I.k) ≤ 2 * ((2 * X + false.toNat) % 2 ^ (64 * Wk I.k))))
    (fun t h7 hk => cOf_ok t (.inr rfl) (by rw [hk .x2 (by decide), k₅.gpr .x2 (by decide), k₄.gpr .x2 (by decide), h2])))
    fun u₆ ⟨v₆, _, o₆, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (by omega) o₆ k₆ (by decide)
  rw [v₅] at v₆
  -- `4 y + 1`.
  refine WP.seq (WP.mono (copyA_ok g₆.ws (o := nTy) (a := nY) (by decide) (by decide) (by decide))
    fun u₇ ⟨v₇, o₇, _, _, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (by omega) o₇ k₇ (by decide)
  rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
    o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), Y₄] at v₇
  refine WP.seq (WP.mono (dbl_ok g₇.ws (a := nTy) (by decide) (b := false) (fun t h7 _ => c0_ok t h7))
    fun u₈ ⟨v₈, _, o₈, k₈⟩ => ?_)
  have g₈ := g₇.out (by decide) (by omega) o₈ k₈ (by decide)
  rw [v₇] at v₈
  refine WP.seq (WP.mono (dbl_ok g₈.ws (a := nTy) (by decide) (b := true) (fun t h7 _ => c1_ok t h7))
    fun u₉ ⟨v₉, _, o₉, k₉⟩ => ?_)
  have g₉ := g₈.out (by decide) (by omega) o₉ k₉ (by decide)
  rw [v₈] at v₉
  -- The difference, and the remainder and root.
  have R₉ : wv u₉.mem I.B (slot (vk I.k) nRm) (vk I.k) = wv u₆.mem I.B (slot (vk I.k) nRm) (vk I.k) := by
    rw [o₉.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₈.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₇.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]
  refine WP.seq (WP.mono (subA_ok g₉.ws (o := nDf) (a := nRm) (b := nTy) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun u₁₀ ⟨v₁₀, h15, _, o₁₀, k₁₀⟩ => ?_)
  have g₁₀ := g₉.out (by decide) (by omega) o₁₀ k₁₀ (by decide)
  rw [R₉, v₆, v₉] at v₁₀
  refine WP.seq (WP.mono (selA_ok g₁₀.ws (o := nRm) (a := nDf) (by decide) (by decide) (by decide) h15)
    fun u₁₁ ⟨v₁₁, o₁₁, k₁₁⟩ => ?_)
  have g₁₁ := g₁₀.out (by decide) (by omega) o₁₁ k₁₁ (by decide)
  have D₁₀ := sub_wsub (wv_lt _ _ _ _) v₁₀
  have r₁₀ : wv u₁₀.mem I.B (slot (vk I.k) nRm) (vk I.k) = wv u₆.mem I.B (slot (vk I.k) nRm) (vk I.k) := by
    rw [o₁₀.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), R₉]
  rw [D₁₀, r₁₀, v₆] at v₁₁
  rw [R₉, v₆, v₉] at v₁₁
  have Y₁₁ : wv u₁₁.mem I.B (slot (vk I.k) nY) (vk I.k) = Y := by
    rw [o₁₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁₀.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₉.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₈.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₇.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), Y₄]
  refine WP.seq (WP.mono (dbl_ok g₁₁.ws (a := nY) (by decide)
    (b := decide (wv u₉.mem I.B (slot (vk I.k) nTy) (vk I.k) ≤ wv u₉.mem I.B (slot (vk I.k) nRm) (vk I.k)))
    (fun t h7 hk => cMask_ok t (by
      rw [hk .x15 (by decide)]; exact (k₁₁.gpr .x15 (by decide)).trans h15)))
    fun u₁₂ ⟨v₁₂, _, o₁₂, k₁₂⟩ => ?_)
  have g₁₂ := g₁₁.out (by decide) (by omega) o₁₂ k₁₂ (by decide)
  rw [Y₁₁, R₉, v₆, v₉] at v₁₂
  refine WP.mono (dec_ok u₁₂ .x6) fun u' ⟨⟨h6, m', _⟩, k₁₃⟩ => ?_
  have F : Frm I.B (rootRanges (vk I.k)) u.mem u'.mem := by
    intro z hz
    have hh := fun r (hr : r ∈ hdrW) => hz r (List.mem_append_left _ hr)
    have rx := hz (slot (Wk I.k) wX4, 8 * Wk I.k) (by simp)
    have rr := hz (slot (vk I.k) nRm, 8 * vk I.k) (by simp)
    have rt := hz (slot (vk I.k) nTy, 8 * vk I.k) (by simp)
    have rd := hz (slot (vk I.k) nDf, 8 * vk I.k) (by simp)
    have ry := hz (slot (vk I.k) nY, 8 * vk I.k) (by simp)
    dsimp only at rx rr rt rd ry
    rw [m', o₁₂ z ry, o₁₁ z rr, o₁₀ z rd, o₉ z rt, o₈ z rt, o₇ z rt, o₆ z rr, o₅ z rr, f₄ z hh, o₃ z rx, o₂ z rx,
      f₁ z hh]
  have hnb : 1 ≤ 64 * vk I.k := by omega
  refine ⟨⟨g₁₂.same m' k₁₃ (by decide), ?_, hI.frm.trans F⟩, ?_⟩
  · rw [Function.iterate_succ_apply', ← hval, sqrtStep_code hnb hXlt, m']
    rw [o₁₂.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₁₁.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₁₀.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₉.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₈.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₇.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₆.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₄ (slot_ge _ _) (by omega), v₃, o₁₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₁₁, v₁₂]
  · rw [h6, k₁₂.gpr .x6 (by decide), k₁₁.gpr .x6 (by decide), k₁₀.gpr .x6 (by decide), k₉.gpr .x6 (by decide),
      k₈.gpr .x6 (by decide), k₇.gpr .x6 (by decide), k₆.gpr .x6 (by decide), k₅.gpr .x6 (by decide),
      k₄.gpr .x6 (by decide), k₃.gpr .x6 (by decide), k₂.gpr .x6 (by decide), k₁.gpr .x6 (by decide)]

/-- `countS`: `x6 := 64 (w + 1)`. -/
theorem countS_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block countS) s fun t => (t.gpr .x6 = BitVec.ofNat 64 (64 * (w + 1)) ∧ t.mem = s.mem) ∧
      Keep [.x6, .x11, .x12] s t := by
  have hw2 := h.w2
  unfold countS
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * (w + 1)) ∧ t.mem = t₁.mem)
    (by brun [h12, ofNat_add_ofNat, shl_ofNat (show (w + 1) * 2 ^ 6 < 2 ^ 64 by omega)]; congr 1; omega)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h6, m₂⟩, k₂⟩ => ⟨⟨h6, m₂.trans m₁⟩, (k₁.trans k₂).mono (by decide)⟩

/-- `sqrt`: `32 W` steps of `sqrtStep` from `(X, 0, 0)`, and the remainder zero and'ed into the mask. -/
theorem sqrt_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) {X : Nat}
    (hX : wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = X) :
    WP isa sqrt s fun t =>
      G I m₀ (vk I.k) (decide (((sqrtStep (64 * vk I.k) (64 * Wk I.k))^[64 * (vk I.k + 1)] (X, 0, 0)).2.1 = 0) && c) t ∧
      wv t.mem I.B (slot (vk I.k) nY) (vk I.k) = ((sqrtStep (64 * vk I.k) (64 * Wk I.k))^[64 * (vk I.k + 1)] (X, 0, 0)).2.2 ∧
      (∀ j k, (j = 0 ∨ j = 1 ∨ (6 ≤ j ∧ j < 12)) → k ≤ vk I.k + 2 →
        wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hv2 : vk I.k ≤ 200 := by have := L.k2; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s2 := slot_lt (w := vk I.k) (show nRm < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show nY < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show nZ < 32 by decide)
  have bX : slot (Wk I.k) wX4 + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bX' : slot (2 * vk I.k + 2) wX4 + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bX
  unfold sqrt
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (h.setNar_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := nRm) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (zeroA_ok g₂.ws (j := nY) (by decide)) fun s₃ ⟨z₃, o₃, _, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (countS_ok g₃.ws) fun s₄ ⟨⟨h6, m₄⟩, k₄⟩ => ?_)
  have g₄ := g₃.same m₄ k₄ (by decide)
  have I0 : SI I m₀ c s₄ (X, 0, 0) 0 s₄ := ⟨g₄, by
    rw [Function.iterate_zero_apply, m₄, o₃.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hX,
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₂]; exact Nat.two_pow_pos _), z₂,
      wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₃]; exact Nat.two_pow_pos _), z₃], Frm.refl _ _ _⟩
  refine WP.seq (WP.mono (wp_countdown (N := 64 * (vk I.k + 1)) (by omega) (by omega) _
    (fun i _ u hI _ => sqrtStepCode_ok L hI) I0 h6) fun s₅ hI => ?_)
  have vR := congrArg (fun p => p.2.1) hI.val
  have vY := congrArg (fun p => p.2.2) hI.val
  simp only at vR vY
  refine WP.mono (zeroA_ok hI.g.ws (j := nZ) (by decide)) fun s₆ ⟨z₆, o₆, _, _, _, k₆⟩ => ?_
  have g₆ := hI.g.out (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok g₆.ws (a := nRm) (b := nZ) (by decide) (by decide))
    fun s₇ ⟨h9, m₇, _, _, k₇⟩ => ?_)
  rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), vR,
    wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₆]; exact Nat.two_pow_pos _), z₆] at h9
  have g₇ := g₆.same m₇ k₇ (by decide)
  refine WP.mono (andZero_ok g₇.ws g₇.msk h9) fun t ⟨⟨mt, _⟩, kt⟩ => ?_
  have ot : Outside I.B (8 * Public.sMask) 8 s₇.mem t.mem := by
    rw [mt]; exact writeW_outside s₇.mem I.B _ (by simp only [Public.sMask, sFn]; omega)
  refine ⟨g₇.store mt kt (by decide), ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (hd_sep (by decide)) (by omega), m₇, o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), vY]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    have e2 : nRm = 2 := rfl
    have e3 : nDf = 3 := rfl
    have e4 : nY = 4 := rfl
    have e5 : nTy = 5 := rfl
    have e5' : nZ = 5 := rfl
    have e7 : wX4 = 7 := rfl
    rw [ot.wv (hd_sep (by decide)) (by omega), m₇, o₆.wv (rd_sep (by omega) hk (by omega)) (by omega)]
    rw [hI.frm.wv_eq (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;>
            exact .inr (by have := slot_ge (vk I.k) j; omega)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact nw_sep (by omega) (by omega) hk (by omega)
          all_goals exact rd_sep (by omega) hk (by omega)) (by omega),
      m₄, o₃.wv (rd_sep (by omega) hk (by omega)) (by omega), o₂.wv (rd_sep (by omega) hk (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]

end VG.Proof.Rsa.AArch64.Rd
