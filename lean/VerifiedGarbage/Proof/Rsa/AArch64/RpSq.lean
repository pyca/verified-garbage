import VerifiedGarbage.Proof.Rsa.AArch64.RpExp
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad

/-!
# `vg_rsa_recover_primes` on AArch64: the squarings

`sqBody`: `x = y²` (in Montgomery form), the masks of `x = 1` and `x = -1`,
and `sqMasks` updates `done`, `ok` and `y` as `RecoverMath.sqStep` does
(`sqBody_ok`); the loop of `64 Bw` of them gives `sqIter`.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel)

/-- `subs` of two registers: the carry is set iff it does not borrow. -/
theorem subs_c (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + (true).toNat) = !decide (a.toNat < b.toNat) := by
  have hb := b.isLt
  have h1 : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := by rw [BitVec.toNat_not]
  rw [h1, Bool.toNat_true]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not, Nat.not_le]; omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

theorem subs_c_ofNat {k t : Nat} (hk : k < 2 ^ 64) (ht : t < 2 ^ 64) :
    decide (2 ^ 64 ≤ k + (~~~BitVec.ofNat 64 t).toNat + (true).toNat) = !decide (k < t) := by
  have := subs_c (BitVec.ofNat 64 k) (BitVec.ofNat 64 t)
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt ht] at this

theorem subs_c_nat {a : Nat} (b : BitVec 64) (ha : a < 2 ^ 64) :
    decide (2 ^ 64 ≤ a + (~~~b).toNat + (true).toNat) = !decide (a < b.toNat) := by
  have := subs_c (BitVec.ofNat 64 a) b
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this

theorem lt_one_iff (x : BitVec 64) : decide (x.toNat < (BitVec.setWidth 64 1#16).toNat) = decide (x = 0) := by
  rw [show (BitVec.setWidth 64 1#16).toNat = 1 from rfl]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
  · intro h; rw [h]; decide

theorem mask_xor_ones (a : Bool) : mask a ^^^ (BitVec.setWidth 64 0#16 - 1#64) = mask (!a) := by
  cases a <;> rfl

/-- `zeroMask` and a store of its mask into header slot `i`. -/
theorem zstore_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    (hc₁ : writesOnly [] (.block [sth .x15 i]) = true := by decide)
    (hc₂ : (Code.block [sth .x15 i] : Prog isa).noCalls = true := by decide)
    (hc₃ : Code.allInstrs keepsV (.block [sth .x15 i] : Prog isa) = true := by decide +kernel) :
    WP isa (.block (zeroMask ++ [sth .x15 i])) s fun u =>
      (u.gpr .x7 = 0 ∧ u.mem = s.mem.writeW (off B (8 * i)) (mask (decide (s.gpr .x9 = 0)))) ∧
        Keep [.x3, .x4, .x7, .x15] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok s) fun u₁ ⟨⟨h15, h7, m₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (8 * i)) (mask (decide (s.gpr .x9 = 0)))) (by
    brun [(k₁.gpr .x0 (by decide)).trans h.x0, hdr_enc hi', (h.scr.congr k₁.wr).st (d := 8 * i) (by omega), h15, m₁])
    hc₁ hc₂ hc₃) fun u ⟨mu, k₂⟩ =>
      ⟨⟨(k₂.gpr .x7 (by decide)).trans h7, mu⟩, (k₁.trans k₂).mono (by decide)⟩

/-- `sqMasks`: the masks of continuing, `done` and `ok`. -/
theorem sqMasks_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k t : Nat} {done ok e1 em : Bool}
    (hk : k < 2 ^ 62) (ht : t < 2 ^ 62)
    (hc1 : word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 t)
    (hc2 : word s.mem B (8 * sC2) = mask done) (hc3 : word s.mem B (8 * sC3) = mask ok)
    (hm : word s.mem B (8 * sMask) = mask e1) (h9 : decide (s.gpr .x9 = 0) = em) :
    WP isa (.block sqMasks) s fun u =>
      (u.gpr .x15 = mask ((!done && decide (k < t)) && !e1 && !(em || decide (k + 1 = t))) ∧
        u.mem = (s.mem.writeW (off B (8 * sC2))
          (mask (done || ((!done && decide (k < t)) && (e1 || (em || decide (k + 1 = t))))))).writeW
            (off B (8 * sC3)) (mask (ok || ((!done && decide (k < t)) && e1)))) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x7, .x10, .x13, .x15] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => h.scr.st (by omega)
  have ek : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have et : (BitVec.ofNat 64 t).toNat = t := by rw [BitVec.toNat_ofNat]; omega
  have ekt : decide (BitVec.ofNat 64 k + 1#64 ^^^ BitVec.ofNat 64 t = 0) = decide (k + 1 = t) := by
    rw [show BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) by rw [BitVec.ofNat_add_ofNat]]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
    · intro e; rw [e]; exact BitVec.xor_self
  have hr3 : ∀ v, (s.mem.writeW (off B (8 * sC2)) v).readW (off B (8 * sC3)) 64 = mask ok := fun v => by
    have := (writeW_outside s.mem B v (d := 8 * sC2) (by simp only [sC2, sFn]; omega)).word
      (d := 8 * sC3) (Or.inr (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC3, sFn]; omega)
    rw [hc3] at this
    exact this
  refine WP.keep [.x1, .x2, .x3, .x4, .x5, .x7, .x10, .x13, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [sqMasks, zeroMask, borrowMask, h.x0, hdr_enc (show sC1 < 32 by decide), hdr_enc (show sT < 32 by decide),
    hdr_enc (show sC2 < 32 by decide), hdr_enc (show sC3 < 32 by decide), hdr_enc (show sMask < 32 by decide),
    hl _ (show sC1 < 32 by decide), hl _ (show sT < 32 by decide), hl _ (show sC2 < 32 by decide),
    hl _ (show sC3 < 32 by decide), hl _ (show sMask < 32 by decide), hs _ (show sC2 < 32 by decide),
    hs _ (show sC3 < 32 by decide), hc1, hT, hc2, hc3, hm, csel_mask', subs_one_c, subs_c, subs_c_ofNat (show k < 2 ^ 64 by omega) (show t < 2 ^ 64 by omega), ek, et,
    Bool.not_not, lt_one_iff,
    h9, ekt, hr3, mask_and', mask_or_mask, mask_xor_ones]
  generalize decide (k < t) = a
  generalize decide (k + 1 = t) = b
  cases a <;> cases b <;> cases done <;> cases ok <;> cases e1 <;> cases em <;> exact ⟨rfl, rfl⟩

/-- `sqNext`: `k += 1` in `sC1`, and `64 Bw - (k + 1)` into `x3`. -/
theorem sqNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el k : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32)
    (hc1 : word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hk : k < 64 * (w + (el + 7) / 8)) :
    WP isa (.block sqNext) s fun u =>
      ((u.gpr .x3).toNat ≠ 0 ↔ k + 1 ≠ 64 * (w + (el + 7) / 8)) ∧
      u.mem = s.mem.writeW (off B (8 * sC1)) (BitVec.ofNat 64 (k + 1)) ∧ Keep [.x3, .x4, .x11, .x12, .x14] s u := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  have hw2 := h.w2
  unfold sqNext
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun u₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : u₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (bw_ok (el := el) (h.scr.congr k₁.wr) h0₁ h256 (by rw [m₁]; exact hel) hel' h12)
    fun u₂ ⟨⟨h14, m₂, _⟩, k₂⟩ => ?_
  have e1 : BitVec.ofNat 64 ((w + (el + 7) / 8) * 2 ^ 6) - BitVec.ofNat 64 (k + 1) =
      BitVec.ofNat 64 (64 * (w + (el + 7) / 8) - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u => u.gpr .x3 = BitVec.ofNat 64 (64 * (w + (el + 7) / 8) - (k + 1)) ∧
      u.mem = s.mem.writeW (off B (8 * sC1)) (BitVec.ofNat 64 (k + 1))) (by
    brun [(k₂.gpr .x0 (by decide)).trans h0₁, h14, hdr_enc (show sC1 < 32 by decide),
      (h.scr.congr (k₁.trans k₂).wr).ld (d := 8 * sC1) (by simp only [sC1, sFn]; omega),
      (h.scr.congr (k₁.trans k₂).wr).st (d := 8 * sC1) (by simp only [sC1, sFn]; omega), m₂, m₁, hc1,
      shl_ofNat (show (w + (el + 7) / 8) * 2 ^ 6 < 2 ^ 64 by omega), BitVec.ofNat_add_ofNat, e1])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h3, mu⟩, k₃⟩ =>
      ⟨by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, mu, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem sqLogic_eq : sqLogic = sqMasks ++ (ws ++ base aX .x16 ++ base aY .x17 ++ [mov .x14 .x12]) := rfl

/-- `ws`, two bases and `x14 := w`. -/
theorem bases2w_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (ws ++ base a .x16 ++ base b .x17 ++ [mov .x14 .x12])) s fun t =>
      (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
        t.mem = s.mem) ∧ Keep [.x11, .x12, .x14, .x16, .x17] s t := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (base2_ok a b .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun t₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = t₂.mem)
    (by brun [(k₂.gpr .x12 (by decide)).trans h12]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h14, m₃⟩, k₃⟩ => ⟨⟨(k₃.gpr .x16 (by decide)).trans h16, (k₃.gpr .x17 (by decide)).trans h17, h14,
      by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- After `k` squarings from `st₀`, from `t₀`: `y` in Montgomery form in
`Y`, and `done` and `ok`. -/
structure SqI (t₀ : State) (B : Addr) (w N tt : Nat) (st₀ : Nat × Bool × Bool) (k : Nat) (u : State) : Prop where
  frm : Frm B (rg w [aAcc, aTmp, aX, aY] [sMask, sC1, sC2, sC3]) t₀.mem u.mem
  keep : Keep mmRegs t₀ u
  y : wv u.mem B (slot w aY) w = (VG.Proof.Rsa.sqIter N tt k st₀).1 * 2 ^ (64 * w) % N
  ylt : (VG.Proof.Rsa.sqIter N tt k st₀).1 < N
  c1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 k
  c2 : word u.mem B (8 * sC2) = mask (VG.Proof.Rsa.sqIter N tt k st₀).2.1
  c3 : word u.mem B (8 * sC3) = mask (VG.Proof.Rsa.sqIter N tt k st₀).2.2

theorem sq_hs : ∀ i ∈ [sMask, sC1, sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- A squaring. -/
theorem sqBody_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t k : Nat}
    {st₀ : Nat × Bool × Bool} (hc : Cst t₀ B Z w minv N el r t) (hk : k < 64 * (w + (el + 7) / 8))
    (hI : SqI t₀ B w N t st₀ k u) :
    WP isa (sqBody M.mm) u fun u' =>
      SqI t₀ B w N t st₀ (k + 1) u' ∧ ((u'.gpr .x3).toNat ≠ 0 ↔ k + 1 ≠ 64 * (w + (el + 7) / 8)) := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have he2 := hc.e2
  have ht2 := hc.t2
  have hR := hc.coprime
  have hN1 : 1 < N := by have := hc.n1; omega
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) sq_hs hI.keep (by decide)
  have hy := hI.y
  have hylt := hI.ylt
  have hc2 := hI.c2
  have hc3 := hI.c3
  have hc1 := hI.c1
  have hst : VG.Proof.Rsa.sqIter N t (k + 1) st₀ = VG.Proof.Rsa.sqStep N t k (VG.Proof.Rsa.sqIter N t k st₀) := rfl
  generalize VG.Proof.Rsa.sqIter N t k st₀ = st at hy hylt hc2 hc3 hst
  obtain ⟨y, done, ok⟩ := st
  dsimp only at hy hylt hc2 hc3
  have hYlt : wv u.mem B (slot w aY) w < N := by rw [hy]; exact Nat.mod_lt _ (by omega)
  rw [show sqBody M.mm = seqs ([copyA aX aY, M.mm aX aX aY] ++ (eqA aX aO ++
    ([.block (zeroMask ++ [sth .x15 sMask])] ++ (eqA aX aNg ++
      [.block sqLogic, VG.Impl.Rsa.AArch64.Crt.selLoop, .block sqNext])))) by
      simp only [sqBody, List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [eqA]) ?_
  simp only [seqs]
  -- `x = y²`.
  refine WP.seq (WP.mono (copyA_ok hcu.ws (o := aX) (a := aY) (by decide) (by decide) (by decide))
    fun u₁ ⟨hx₁, o₁, _, _, k₁⟩ => ?_)
  have hf₁ : Frm B (rg w [aX] []) u.mem u₁.mem := Frm.rg_of_out o₁ (by omega) _ _ (by decide)
  have hc₁ := hcu.congr hf₁ (by decide) (by simp) k₁ (by decide)
  have hY₁ : wv u₁.mem B (slot w aY) w = wv u.mem B (slot w aY) w :=
    hf₁.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
  have hg₁ := hc₁.good
  refine WP.mono (M.mm_ok hg₁.1 hg₁.2 hw1 (by omega) (o := aX) (a := aX) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.hinv
    (by rw [hY₁, hc₁.hn]; exact hYlt)) fun u₂ ⟨_, hlt₂, hm₂, ha₂, k₂⟩ => ?_
  rw [hc₁.hn] at hlt₂ hm₂
  rw [hx₁, hY₁] at hm₂
  have hX₂ : wv u₂.mem B (slot w aX) w = y * y % N * 2 ^ (64 * w) % N := VG.Proof.Rsa.sq_mont hR hy hlt₂ hm₂
  have hf₂ : Frm B (rg w [aAcc, aTmp, aX] []) u₁.mem u₂.mem := Frm.rg_of_arrays ha₂ _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hxN : y * y % N < N := Nat.mod_lt _ (by omega)
  -- `x = 1`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₂.ws (a := aX) (b := aO) (by decide)
    (by decide)) fun u₃ ⟨hz₃, m₃, _, _, k₃⟩ => ?_)
  rw [hX₂, hc₂.ho, VG.Proof.Rsa.eq_one_mont hR hN1 hxN rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (zstore_ok hc₃.ws (i := sMask) (by decide) (by decide))
    fun u₄ ⟨⟨_, m₄⟩, k₄⟩ => ?_)
  have he1 : decide (u₃.gpr .x9 = 0) = decide (y * y % N = 1) := decide_eq_decide.mpr hz₃
  rw [he1] at m₄
  have hf₄ : Frm B (rg w [] [sMask]) u₃.mem u₄.mem := by
    rw [m₄]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₄ := hc₃.congr hf₄ (by decide) (by decide) k₄ (by decide)
  -- `x = -1`.
  have hX₄ : wv u₄.mem B (slot w aX) w = wv u₂.mem B (slot w aX) w := by
    rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₃]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₄.ws (a := aX) (b := aNg) (by decide)
    (by decide)) fun u₅ ⟨hz₅, m₅, _, _, k₅⟩ => ?_)
  rw [hX₄, hX₂, hc₄.hng, VG.Proof.Rsa.eq_neg_mont hR hN1 hxN rfl] at hz₅
  have hc₅ := hc₄.congr (js := []) (hs := []) (by rw [m₅]; exact Frm.refl _ _ _) (by simp) (by simp) k₅ (by decide)
  have hem : decide (u₅.gpr .x9 = 0) = decide (y * y % N = N - 1) := decide_eq_decide.mpr hz₅
  -- The masks.
  have hw5 : ∀ i, i < 32 → i ≠ sMask → word u₅.mem B (8 * i) = word u.mem B (8 * i) := fun i hi hne => by
    rw [m₅, hf₄.rg_word hi (by simpa using hne), m₃, hf₂.rg_word hi (by simp), hf₁.rg_word hi (by simp)]
  have hm₅ : word u₅.mem B (8 * sMask) = mask (decide (y * y % N = 1)) := by rw [m₅, m₄, word_writeW_self]
  simp only [seqs]
  rw [sqLogic_eq]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (sqMasks_ok hc₅.ws (k := k) (t := t) (done := done) (ok := ok)
    (by omega) (by omega) (by rw [hw5 _ (by decide) (by decide)]; exact hc1) hc₅.ht
    (by rw [hw5 _ (by decide) (by decide)]; exact hc2) (by rw [hw5 _ (by decide) (by decide)]; exact hc3) hm₅ hem)
    fun u₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ?_))
  have hf₆ : Frm B (rg w [] [sC2, sC3]) u₅.mem u₆.mem := by
    rw [m₆]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hc₆ := hc₅.congr hf₆ (by decide) (by decide) k₆ (by decide)
  refine WP.mono (bases2w_ok hc₆.ws aX aY) fun u₇ ⟨⟨h16, h17, h14, m₇⟩, k₇⟩ => ?_
  have hc₇ := hc₆.congr (js := []) (hs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇ (by decide)
  have h15₇ : u₇.gpr .x15 = _ := (k₇.gpr .x15 (by decide)).trans h15₆
  -- `y := x` if the squarings continue.
  have sY := hc₇.ws.sl (j := aY) (by decide)
  have sX := hc₇.ws.sl (j := aX) (by decide)
  refine WP.seq (WP.mono (selLoop_ok hc₇.ws.scr h16 h17 h14 h15₇ (by omega) (by omega) (by omega) (by omega)
    (by have := slot_sep (w := w) (show aY ≠ aX by decide); omega)) fun u₈ ⟨hy₈, o₈, k₈⟩ => ?_)
  have hf₈ : Frm B (rg w [aY] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have hc₈ := hc₇.congr hf₈ (by decide) (by simp) k₈ (by decide)
  -- `k += 1`.
  have hc1₈ : word u₈.mem B (8 * sC1) = BitVec.ofNat 64 k := by
    rw [hf₈.rg_word (by decide) (by simp), m₇, hf₆.rg_word (by decide) (by decide),
      hw5 _ (by decide) (by decide)]; exact hc1
  refine WP.mono (sqNext_ok hc₈.ws hc₈.hel (by omega) hc1₈ hk) fun u' ⟨hz, m₉, k₉⟩ => ⟨?_, hz⟩
  have hf₉ : Frm B (rg w [] [sC1]) u₈.mem u'.mem := by
    rw [m₉]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hfu₅ : Frm B (rg w [aX, aAcc, aTmp, aX] [sMask]) u.mem u₅.mem := by
    have := ((hf₁.rg_trans hf₂).rg_trans (js' := []) (hs' := [])
      (by rw [m₃]; exact Frm.refl _ _ _ : Frm B (rg w [] []) u₂.mem u₃.mem)).rg_trans hf₄
    rw [← m₅] at this
    exact this.rg_mono (by decide) (by decide)
  -- The values after the squaring.
  have hY₈ : wv u₈.mem B (slot w aY) w = (if ((!done && decide (k < t)) && !decide (y * y % N = 1) &&
      !(decide (y * y % N = N - 1) || decide (k + 1 = t))) then y * y % N else y) * 2 ^ (64 * w) % N := by
    have hXu₆ : wv u₆.mem B (slot w aX) w = y * y % N * 2 ^ (64 * w) % N := by
      rw [hf₆.rg_wv hZ16 (j := aX) (by decide) (by decide) (by decide) (by omega), m₅, hX₄, hX₂]
    have hYu₆ : wv u₆.mem B (slot w aY) w = y * 2 ^ (64 * w) % N := by
      rw [hf₆.rg_wv hZ16 (j := aY) (by decide) (by decide) (by decide) (by omega), m₅,
        hf₄.rg_wv hZ16 (j := aY) (by decide) (by decide) (by decide) (by omega), m₃,
        hf₂.rg_wv hZ16 (j := aY) (by decide) (by decide) (by decide) (by omega), hY₁, hy]
    rw [hy₈, m₇, hXu₆, hYu₆]
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hI.frm.rg_trans hfu₅).rg_trans hf₆).rg_trans (by rw [m₇]; exact Frm.refl _ _ _ :
      Frm B (rg w [] []) u₆.mem u₇.mem)).rg_trans hf₈).rg_trans hf₉).rg_mono (by decide) (by decide)
  · exact ((((((((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans
      k₉).mono (by decide))
  · rw [hst, hf₉.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₈]
    simp only [VG.Proof.Rsa.sqStep]
  · rw [hst]
    simp only [VG.Proof.Rsa.sqStep]
    split <;> omega
  · rw [m₉, word_writeW_self]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆]
    rw [(writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hst]
    simp only [VG.Proof.Rsa.sqStep]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆, word_writeW_self, hst]
    simp only [VG.Proof.Rsa.sqStep]

end VG.Proof.Rsa.AArch64
