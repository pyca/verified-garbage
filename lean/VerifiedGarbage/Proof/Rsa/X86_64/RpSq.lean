import VerifiedGarbage.Proof.Rsa.X86_64.RpExp

/-!
# `vg_rsa_recover_primes` on x86-64: the squarings

`sqBody`: `x = y²` (in Montgomery form), the masks of `x = 1` and `x = -1`,
and `sqLogic` updates `done`, `ok` and `y` as `RecoverMath.sqStep` does
(`sqBody_ok`); the loop of `64 Bw` of them gives `sqIter` (`sqLoop_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Proof.Bignum (mont_cancel mont_sq)

theorem mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> rfl

theorem mask_not (a : Bool) : mask a ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = mask (!a) := by
  cases a <;> rfl

theorem sbb_mask (c : Bool) : 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := rfl

theorem xor_lt_one (a b : BitVec 64) : decide ((a ^^^ b).toNat < (1 : BitVec 64).toNat) = decide (a = b) := by
  rw [decide_lt_one']
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  constructor
  · intro h; exact BitVec.xor_eq_zero_iff.mp h
  · intro h; rw [h, BitVec.xor_self]; rfl

/-- `eqStore i`: the mask of `rbp = 0` into header slot `i`. -/
theorem eqStore_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32) :
    WP isa (.block (eqStore i)) s fun u =>
      u.mem = s.mem.writeW (off B (8 * i)) (mask (decide (s.gpr .rbp = 0))) ∧ Keep [.rax, .rbp] s u := by
  have h256 := h.h256
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun u => u.mem = s.mem.writeW (off B (8 * i))
      (mask (decide (s.gpr .rbp = 0)))) (by
    unfold eqStore
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.st (d := 8 * i) (by omega), decide_lt_one', sbb_mask]) rfl)
    fun u ⟨a, b⟩ => ⟨a, b⟩

/-- `sqNext`: `k += 1` in `sC1`, against `64 Bw`. -/
theorem sqNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el k : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32)
    (hc1 : word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hk : k < 64 * (w + (el + 7) / 8)) :
    WP isa (.block sqNext) s fun u =>
      u.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧
      u.mem = s.mem.writeW (off B (8 * sC1)) (BitVec.ofNat 64 (k + 1)) ∧ Keep [.rax, .rdx] s u := by
  have h256 := h.h256
  have hw2 := h.w2
  unfold sqNext
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.gpr .rdx = BitVec.ofNat 64 (k + 1) ∧
      u.mem = s.mem.writeW (off B (8 * sC1)) (BitVec.ofNat 64 (k + 1))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega),
      h.scr.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hc1, ofNat_add_one]) rfl)
    fun u₁ ⟨⟨hdx, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  have hf₁ : Frm B (rg w [] [sC1]) s.mem u₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hw₁ : Ws u₁ B Z w := h.congrG hf₁ (by decide) k₁ (by decide)
  refine WP.mono (bw_ok hw₁ (by rw [hf₁.rg_word (by decide) (by decide)]; exact hel) hel')
    fun u₂ ⟨hax, m₂, k₂⟩ => ?_
  have hdx₂ : u₂.gpr .rdx = BitVec.ofNat 64 (k + 1) := (k₂.gpr (by decide)).trans hdx
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧
      u.mem = u₂.mem) (by
    simp only [List.replicate, List.cons_append, List.nil_append]
    xrun [hax, hdx₂, ofNat_dbl, dbl6, ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega)
      (show 64 * (w + (el + 7) / 8) < 2 ^ 64 by omega)]) rfl)
    fun u ⟨⟨hz, mu⟩, k₃⟩ => ⟨hz, by rw [mu, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## The squaring's arithmetic -/

theorem mont_inj {x y R N : Nat} (hR : Nat.Coprime R N) (hx : x < N) (hy : y < N)
    (h : x * R % N = y * R % N) : x = y := by
  have := mont_cancel hR h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem mod_ne_zero_of_coprime {R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) : R % N ≠ 0 := by
  intro h
  have := Nat.Coprime.eq_one_of_dvd hR.symm (Nat.dvd_of_mod_eq_zero h)
  omega

/-- `-1` in Montgomery form. -/
theorem neg_one_mont {R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) : (N - 1) * R % N = N - R % N := by
  have ha := mod_ne_zero_of_coprime hR hN
  have hlt := Nat.mod_lt R (show 0 < N by omega)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, R % (M + 1) = b + 1 := ⟨R % (M + 1) - 1, by omega⟩
  have hR' := Nat.div_add_mod R (M + 1)
  rw [hb] at hR' hlt ⊢
  have e : M * R = (M + 1) * (M * (R / (M + 1)) + b) + (M - b) := by
    conv => lhs; rw [← hR']
    rw [Nat.mul_add, Nat.mul_succ, Nat.mul_left_comm M (M + 1), Nat.mul_add (M + 1), Nat.succ_mul M b]
    omega
  rw [Nat.add_sub_cancel, e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `x = 1` and `x = -1` from Montgomery forms. -/
theorem eq_one_mont {X x R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) (hx : x < N) (hX : X = x * R % N) :
    X = R % N ↔ x = 1 := by
  subst hX
  constructor
  · intro h; exact mont_inj hR hx hN (by rw [h, Nat.one_mul])
  · intro h; rw [h, Nat.one_mul]

theorem eq_neg_mont {X x R N : Nat} (hR : Nat.Coprime R N) (hN : 1 < N) (hx : x < N) (hX : X = x * R % N) :
    X = N - R % N ↔ x = N - 1 := by
  subst hX
  rw [← neg_one_mont hR hN]
  constructor
  · intro h; exact mont_inj hR hx (by omega) h
  · intro h; rw [h]

/-- `sqLogic`'s masks, for `sC1 = k`, `t`, `done`, `ok`, `x = 1` (`e1`) and
`x = -1` (`em`, from `rbp`): `done` and `ok` updated, and `rbp` the mask of
not continuing. -/
theorem sqMasks_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k t : Nat} {done ok e1 em : Bool}
    (hk : k < 2 ^ 62) (ht : t < 2 ^ 62)
    (hc1 : word s.mem B (8 * sC1) = BitVec.ofNat 64 k) (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 t)
    (hc2 : word s.mem B (8 * sC2) = mask done) (hc3 : word s.mem B (8 * sC3) = mask ok)
    (hm : word s.mem B (8 * sMask) = mask e1) (hbp : decide (s.gpr .rbp = 0) = em) :
    WP isa (.block (sqLogic.take 29)) s fun u =>
      u.gpr .rbp = mask (!((!done && decide (k < t)) && !e1 && !(em || decide (k + 1 = t)))) ∧
      u.mem = (s.mem.writeW (off B (8 * sC2))
        (mask (done || ((!done && decide (k < t)) && (e1 || (em || decide (k + 1 = t))))))).writeW
          (off B (8 * sC3)) (mask (ok || ((!done && decide (k < t)) && e1))) ∧
      Keep [.rax, .rcx, .rdx, .r15, .rbp] s u := by
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => h.scr.st (by omega)
  have ek : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have et : (BitVec.ofNat 64 t).toNat = t := by rw [BitVec.toNat_ofNat]; omega
  have ekt : decide (BitVec.ofNat 64 k + 1 ^^^ BitVec.ofNat 64 t = 0) = decide (k + 1 = t) := by
    rw [ofNat_add_one]
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
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r15, .rbp] (Q := fun u =>
      u.gpr .rbp = mask (!((!done && decide (k < t)) && !e1 && !(em || decide (k + 1 = t)))) ∧
      u.mem = (s.mem.writeW (off B (8 * sC2))
        (mask (done || ((!done && decide (k < t)) && (e1 || (em || decide (k + 1 = t))))))).writeW
          (off B (8 * sC3)) (mask (ok || ((!done && decide (k < t)) && e1)))) ?_ (by decide))
    fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  simp only [sqLogic, List.take, List.cons_append]
  xrun [State.ea, hdr, h.rdi, hdrOff, hl _ (show sC1 < 32 by decide), hl _ (show sT < 32 by decide),
    hl _ (show sC2 < 32 by decide), hl _ (show sC3 < 32 by decide), hl _ (show sMask < 32 by decide),
    hs _ (show sC2 < 32 by decide), hs _ (show sC3 < 32 by decide), hc1, hT, hc2, hc3, hm, decide_lt_one', hbp,
    sbb_mask, mask_and', mask_or, mask_not, xor_lt_one, ek, et, ekt, hr3]
  generalize decide (k < t) = a
  generalize decide (k + 1 = t) = b
  cases a <;> cases b <;> cases done <;> cases ok <;> cases e1 <;> cases em <;> exact ⟨rfl, rfl⟩

/-- `ws ++ base a .r8 ++ base b .rsi`. -/
theorem bases2_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b : Nat) :
    WP isa (.block (ws ++ base a .r8 ++ base b .rsi)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B (slot w a) ∧ t.gpr .rsi = off B (slot w b) ∧
      t.mem = s.mem ∧ Keep [.r12, .r9, .r8, .rsi] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun t₂ ⟨h8, m₂, k₂⟩ => ?_
  refine WP.mono (base_ok b (r := .rsi) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t ⟨hsi, m₃, k₃⟩ => ⟨?_, ?_, hsi, by rw [m₃, m₂, m₁],
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · exact (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  · exact (k₃.gpr (by decide)).trans h8

theorem sqLogic_eq : sqLogic = sqLogic.take 29 ++ (ws ++ base aY .r8 ++ base aX .rsi) := rfl

/-- After `k` squarings from `st₀`, from `t₀`: `y` in Montgomery form in
`Y`, and `done` and `ok`. -/
structure SqI (t₀ : State) (B : Addr) (w N tt : Nat) (st₀ : Nat × Bool × Bool) (k : Nat) (u : State) : Prop where
  frm : Frm B (rg w [aAcc, aTmp, aX, aY] [sMask, sC1, sC2, sC3]) t₀.mem u.mem
  keep : Keep mmRegs t₀ u
  y : wv u.mem B (slot w aY) w = (sqIter N tt k st₀).1 * 2 ^ (64 * w) % N
  ylt : (sqIter N tt k st₀).1 < N
  c1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 k
  c2 : word u.mem B (8 * sC2) = mask (sqIter N tt k st₀).2.1
  c3 : word u.mem B (8 * sC3) = mask (sqIter N tt k st₀).2.2

theorem sq_hs : ∀ i ∈ [sMask, sC1, sC2, sC3], rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- The square in Montgomery form. -/
theorem sq_mont {X Y y R N : Nat} (hR : Nat.Coprime R N) (hY : Y = y * R % N) (hX : X < N)
    (h : X * R % N = Y * Y % N) : X = y * y % N * R % N := by
  have e : X % N = y * y % N * R % N := by
    apply mont_cancel hR
    rw [h, hY, ← Nat.mul_mod, Nat.mul_assoc (y * y % N), Nat.mod_mul_mod, Nat.mul_mul_mul_comm]
  rwa [Nat.mod_eq_of_lt hX] at e

/-- A squaring. -/
theorem sqBody_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t k : Nat}
    {st₀ : Nat × Bool × Bool} (hc : Cst t₀ B Z w minv N el r t) (hk : k < 64 * (w + (el + 7) / 8))
    (hI : SqI t₀ B w N t st₀ k u) :
    WP isa (sqBody M.mm) u fun u' =>
      u'.zf = some (decide (k + 1 = 64 * (w + (el + 7) / 8))) ∧ SqI t₀ B w N t st₀ (k + 1) u' := by
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
  have hst : sqIter N t (k + 1) st₀ = sqStep N t k (sqIter N t k st₀) := rfl
  generalize sqIter N t k st₀ = st at hy hylt hc2 hc3 hst
  obtain ⟨y, done, ok⟩ := st
  dsimp only at hy hylt hc2 hc3
  have hYlt : wv u.mem B (slot w aY) w < N := by rw [hy]; exact Nat.mod_lt _ (by omega)
  rw [show sqBody M.mm = seqs ([copyA aX aY, M.mm aX aX aY] ++ (eqA aX aO ++ ([.block (eqStore sMask)] ++
    (eqA aX aNg ++ [.block sqLogic, wordLoop 0 selBody, .block sqNext])))) by
      simp only [sqBody, List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  -- `x = y²`.
  refine WP.seq (WP.mono (copyA_ok hcu.ws (o := aX) (a := aY) (by decide) (by decide) (by decide))
    fun u₁ ⟨hx₁, o₁, k₁⟩ => ?_)
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
  have hX₂ : wv u₂.mem B (slot w aX) w = y * y % N * 2 ^ (64 * w) % N := sq_mont hR hy hlt₂ hm₂
  have hf₂ : Frm B (rg w [aAcc, aTmp, aX] []) u₁.mem u₂.mem := Frm.rg_of_arrays ha₂ _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hxN : y * y % N < N := Nat.mod_lt _ (by omega)
  -- `x = 1`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₂.ws (a := aX) (b := aO) (by decide)
    (by decide)) fun u₃ ⟨hz₃, m₃, k₃⟩ => ?_)
  rw [hX₂, hc₂.ho, eq_one_mont hR hN1 hxN rfl] at hz₃
  have hc₃ := hc₂.congr (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) (by simp) k₃ (by decide)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (eqStore_ok hc₃.ws (i := sMask) (by decide) (by decide))
    fun u₄ ⟨m₄, k₄⟩ => ?_)
  have he1 : decide (u₃.gpr .rbp = 0) = decide (y * y % N = 1) := decide_eq_decide.mpr hz₃
  rw [he1] at m₄
  have hf₄ : Frm B (rg w [] [sMask]) u₃.mem u₄.mem := by
    rw [m₄]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hc₄ := hc₃.congr hf₄ (by decide) (by decide) k₄ (by decide)
  -- `x = -1`.
  have hX₄ : wv u₄.mem B (slot w aX) w = wv u₂.mem B (slot w aX) w := by
    rw [hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₃]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok hc₄.ws (a := aX) (b := aNg) (by decide)
    (by decide)) fun u₅ ⟨hz₅, m₅, k₅⟩ => ?_)
  rw [hX₄, hX₂, hc₄.hng, eq_neg_mont hR hN1 hxN rfl] at hz₅
  have hc₅ := hc₄.congr (js := []) (hs := []) (by rw [m₅]; exact Frm.refl _ _ _) (by simp) (by simp) k₅ (by decide)
  have hem : decide (u₅.gpr .rbp = 0) = decide (y * y % N = N - 1) := decide_eq_decide.mpr hz₅
  -- The masks.
  have hw5 : ∀ i, i < 32 → i ≠ sMask → word u₅.mem B (8 * i) = word u.mem B (8 * i) := fun i hi hne => by
    rw [m₅, hf₄.rg_word hi (by simpa using hne), m₃, hf₂.rg_word hi (by simp), hf₁.rg_word hi (by simp)]
  have hm₅ : word u₅.mem B (8 * sMask) = mask (decide (y * y % N = 1)) := by rw [m₅, m₄, word_writeW_self]
  simp only [seqs]
  rw [sqLogic_eq]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (sqMasks_ok hc₅.ws (k := k) (t := t) (done := done) (ok := ok) (by omega) (by omega)
    (by rw [hw5 _ (by decide) (by decide)]; exact hc1) hc₅.ht (by rw [hw5 _ (by decide) (by decide)]; exact hc2)
    (by rw [hw5 _ (by decide) (by decide)]; exact hc3) hm₅ hem) fun u₆ ⟨hbp₆, m₆, k₆⟩ => ?_))
  have hf₆ : Frm B (rg w [] [sC2, sC3]) u₅.mem u₆.mem := by
    rw [m₆]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3] (by decide))
  have hc₆ := hc₅.congr hf₆ (by decide) (by decide) k₆ (by decide)
  refine WP.mono (bases2_ok hc₆.ws aY aX) fun u₇ ⟨h12, h8, hsi, m₇, k₇⟩ => ?_
  have hc₇ := hc₆.congr (js := []) (hs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇ (by decide)
  have hbp₇ : u₇.gpr .rbp = _ := (k₇.gpr (by decide)).trans hbp₆
  -- `y := x` if the squarings continue.
  have sY := hc₇.ws.sl (j := aY) (by decide)
  have sX := hc₇.ws.sl (j := aX) (by decide)
  refine WP.seq (WP.mono (sel_ok hc₇.ws.scr h8 hsi hbp₇ h12 (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) (show aY ≠ aX by decide); omega)) fun u₈ ⟨hy₈, o₈, k₈⟩ => ?_)
  have hf₈ : Frm B (rg w [aY] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have hc₈ := hc₇.congr hf₈ (by decide) (by simp) k₈ (by decide)
  -- `k += 1`.
  have hc1₈ : word u₈.mem B (8 * sC1) = BitVec.ofNat 64 k := by
    rw [hf₈.rg_word (by decide) (by simp), m₇, hf₆.rg_word (by decide) (by decide),
      hw5 _ (by decide) (by decide)]; exact hc1
  refine WP.mono (sqNext_ok hc₈.ws hc₈.hel (by omega) hc1₈ hk) fun u' ⟨hz, m₉, k₉⟩ => ⟨hz, ?_⟩
  have hf₉ : Frm B (rg w [] [sC1]) u₈.mem u'.mem := by
    rw [m₉]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hfu₅ : Frm B (rg w [aX, aAcc, aTmp, aX] [sMask]) u.mem u₅.mem := by
    have := ((hf₁.rg_trans hf₂).rg_trans (js' := []) (hs' := [])
      (by rw [m₃]; exact Frm.refl _ _ _ : Frm B (rg w [] []) u₂.mem u₃.mem)).rg_trans hf₄
    rw [← m₅] at this
    exact this.rg_mono (by decide) (by decide)
  -- The values after the squaring.
  have hY₈ : wv u₈.mem B (slot w aY) w = (if !((!done && decide (k < t)) && !decide (y * y % N = 1) &&
      !(decide (y * y % N = N - 1) || decide (k + 1 = t))) then y else y * y % N) * 2 ^ (64 * w) % N := by
    rw [hy₈, m₇, hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
      hf₆.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₅, hX₄,
      hf₄.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₃,
      hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₁, hy, hX₂]
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hI.frm.rg_trans hfu₅).rg_trans hf₆).rg_trans (by rw [m₇]; exact Frm.refl _ _ _ :
      Frm B (rg w [] []) u₆.mem u₇.mem)).rg_trans hf₈).rg_trans hf₉).rg_mono (by decide) (by decide)
  · exact ((((((((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans
      k₉).mono (by decide))
  · rw [hst, hf₉.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY₈]
    simp only [sqStep]
    by_cases hcnd : ((!done && decide (k < t)) && !decide (y * y % N = 1) &&
        !(decide (y * y % N = N - 1) || decide (k + 1 = t))) = true
    · simp only [hcnd, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    · simp only [Bool.not_eq_true] at hcnd
      simp only [hcnd, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
  · rw [hst]
    simp only [sqStep]
    split <;> omega
  · rw [m₉, word_writeW_self]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆]
    rw [(writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hst]
    simp only [sqStep]
  · rw [hf₉.rg_word (by decide) (by decide), hf₈.rg_word (by decide) (by simp), m₇, m₆, word_writeW_self, hst]
    simp only [sqStep]

end VG.Proof.Rsa.X86_64
