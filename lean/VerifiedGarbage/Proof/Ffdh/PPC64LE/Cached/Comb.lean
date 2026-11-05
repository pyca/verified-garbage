module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Digit
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Cut
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad

/-! # FFDH's context on PPC64LE: the comb's selection

`selEntry_ok`: entry `e` of the context into array 3, then array `o :=` it
if `e` is the digit, else array `t`. `select_ok`: array 4 `:=` the digit's
entry, reading every entry. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env envRegs sel_ok selRegs arr)
open VG.Proof.Bignum (slot slot_sep)

/-- The context's words. -/
abbrev ctxWords (w : Nat) : Nat := 3 + 34 * w

/-- The context at `C`: readable and apart from the working space. -/
structure CtxRd (s : State) (B : Addr) (Z : Nat) (C : Addr) (w : Nat) : Prop where
  hn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64
  rd : ∀ d, d + 8 ≤ 8 * ctxWords w → InRegions (s.rd ++ s.wr) (off C d) 8
  sep : ∀ x, ofs C x < 8 * ctxWords w → Z ≤ ofs B x

/-- A change of the working space keeps the context. -/
theorem outs_ctx {B C : Addr} {Z n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (hsep : ∀ x, ofs C x < n → Z ≤ ofs B x) : Outside C n (2 ^ 64) m m' :=
  fun x hx => h x fun r hr' => Or.inr (by
    rcases hx with hx | hx
    · have := hsep x hx; have := hr r hr'; omega
    · have := (x - C).isLt; simp only [ofs] at hx; omega)

theorem CtxRd.congr {s t : State} {B : Addr} {Z : Nat} {C : Addr} {w : Nat} (h : CtxRd s B Z C w)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxRd t B Z C w :=
  ⟨h.hn, fun d hd => by rw [hrd, hwr]; exact h.rd d hd, h.sep⟩

/-- Words that agree are numbers that agree. -/
theorem wordsVal_of_words' {m m' : Mem} {B B' : Addr} : ∀ {d d' k : Nat},
    (∀ i < k, word m B (d + 8 * i) = word m' B' (d' + 8 * i)) → wordsVal m B d k = wordsVal m' B' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_of_words' (d := d + 8) (d' := d' + 8) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega, show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega] at this]

theorem val32_of_words {m m' : Mem} {B B' : Addr} {d d' k : Nat}
    (h : ∀ i < k, word m B (d + 8 * i) = word m' B' (d' + 8 * i)) : val32 m B d (2 * k) = val32 m' B' d' (2 * k) := by
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32]; exact wordsVal_of_words' h

/-- Entry `a` of the context at `C`, as a number. -/
abbrev ent (m : Mem) (C : Addr) (w a : Nat) : Nat := val32 m C (rowOff w (a + 2)) (2 * w)

theorem row_fits {w e : Nat} (he : e < 32) : rowOff w (e + 2) + 8 * w ≤ 8 * ctxWords w := by
  have h1 := Nat.mul_le_mul_left w (show e + 2 + 1 ≤ 34 by omega)
  rw [Nat.mul_succ, Nat.mul_comm w 34] at h1
  unfold rowOff ctxWords; omega

/-- The registers `selEntry` writes. -/
def selERegs : List Reg := [.r0, .r3, .r4, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r25]

/-- What `selEntry` changes. -/
abbrev selEOut (w o : Nat) : List (Nat × Nat) := [(slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))]

/-- `selEntry o t`: entry `e` (`r25`) to array `o` if it is the digit `d`
(`r26`), else array `t`; `e` advanced. -/
theorem selEntry_ok {s : State} {B C : Addr} {Z w e d o t : Nat} (h : Env s B Z w) (h30 : s.gpr .r30 = C)
    (hc : CtxRd s B Z C w) (h25 : s.gpr .r25 = BitVec.ofNat 64 e) (h26 : s.gpr .r26 = BitVec.ofNat 64 d)
    (he : e < 32) (hd : d < 32) (ho : o < 28) (ht : t < 28) (ho3 : o ≠ 3) (ht3 : t ≠ 3) (hot : o ≠ t) :
    WP isa (selEntry o t) s fun u =>
      (arr u.mem B w o = (if e = d then ent s.mem C w e else arr s.mem B w t) ∧
        u.gpr .r25 = BitVec.ofNat 64 (e + 1) ∧ Outs B (selEOut w o) s.mem u.mem) ∧
      Keep selERegs s u := by
  have hw := h.hw; have hw' := h.hw'; have hZ := h.hZ
  have hnw := h.hs.nowrap
  have haO := h.arr ho; have haT := h.arr ht; have ha3 := h.arr (show 3 < 28 by decide)
  unfold selEntry
  -- `r3 := e + 2`.
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (e + 2) ∧ u.mem = s.mem)
    (by prun [h25, ofNat_add']) (by decide)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  refine WP.seq (WP.mono (loadRow_ok (a := 3) (Zc := 8 * ctxWords w) e1 ((k1.gpr .r30 (by decide)).trans h30)
    a3 (by decide) (by omega) (row_fits he) hc.hn
    (fun i hi => by rw [k1.rd, k1.wr]; exact hc.rd _ (by have := row_fits (w := w) he; unfold rowOff ctxWords at *; omega))
    hc.sep) fun s₂ ⟨⟨w2, o2⟩, k2⟩ => ?_)
  rw [m1] at w2 o2
  have k12 := k1.trans k2
  have e2 := e1.keep k2 (by decide)
  -- The mask of `e = d`.
  refine WP.seq (WP.mono (WP.keep [.r0, .r4, .r20] (Q := fun u =>
      u.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if decide (e = d) then 1 else 0) ∧ u.mem = s₂.mem)
    (by prun [(k12.gpr .r25 (by decide)).trans h25, (k12.gpr .r26 (by decide)).trans h26,
      GenerateKey.eq_mask (show e < 2 ^ 32 by omega) (show d < 2 ^ 32 by omega)])
    (by decide)) fun s₃ ⟨⟨a20, m3⟩, k3⟩ => ?_)
  have e3 := e2.keep k3 (by decide)
  refine WP.seq (WP.mono (sel_ok e3 ho (by decide : 3 < 28) ht ho3 hot a20) fun s₄ ⟨⟨v4, o4⟩, k4⟩ => ?_)
  rw [m3] at v4 o4
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (WP.keep [.r25] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 (e + 1) ∧ u.mem = s₄.mem)
    (by prun [(k14.gpr .r25 (by decide)).trans h25, ofNat_add']) (by decide)) fun u ⟨⟨u25, um⟩, uk⟩ =>
      ⟨⟨?_, u25, ?_⟩, (k14.trans uk).mono (by decide)⟩
  · simp only [arr] at v4 ⊢
    rw [um, v4]
    by_cases hb : e = d
    · subst hb
      simp only [decide_true, ↓reduceIte]
      exact val32_of_words w2
    · simp only [hb, decide_false, ↓reduceIte, Bool.false_eq_true]
      exact Outside.val32 o2 (by have := slot_sep (w := w) ht3; omega) (by omega)
  · have o2' : Outs B (selEOut w o) s.mem s₂.mem :=
      Outs.of_outside (o2.mono (o' := slot w 3) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [selEOut])
    have o4' : Outs B (selEOut w o) s₂.mem s₄.mem := Outs.of_outside o4 (by simp [selEOut])
    rw [um]
    exact o2'.trans o4'

/-- What `select` changes: arrays 3 to 5. -/
abbrev selOut (w : Nat) : List (Nat × Nat) := [(slot w 3, 3 * (8 * (w + 2)))]

theorem selEOut_cover (w : Nat) {o : Nat} (ho : o = 4 ∨ o = 5) :
    ∀ r ∈ selEOut w o, ∃ R ∈ selOut w, R.1 ≤ r.1 ∧ r.1 + r.2 ≤ R.1 + R.2 := by
  intro r hr
  simp only [selEOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp only; omega⟩
  · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [slot] <;> rcases ho with rfl | rfl <;> omega

theorem ofNat_sub_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := by
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega
    have hb : (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = false := beq_false_of_ne hne
    simp only [bne, hb, Bool.not_false, h, ne_eq, not_false_eq_true, decide_true]

theorem wordsVal_zero' {m : Mem} {B : Addr} : ∀ {d k : Nat}, (∀ i < k, word m B (d + 8 * i) = 0) → wordsVal m B d k = 0
  | _, 0, _ => rfl
  | d, k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_zero' (d := d + 8) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega] at this]
    rfl

/-- The selection after the entries below `e`, from `s₀`. -/
structure SelI (s₀ : State) (B C : Addr) (Z w d e : Nat) (u : State) : Prop where
  env : Env u B Z w
  h30 : u.gpr .r30 = C
  ctx : CtxRd u B Z C w
  h25 : u.gpr .r25 = BitVec.ofNat 64 e
  h26 : u.gpr .r26 = BitVec.ofNat 64 d
  acc : arr u.mem B w 4 = if d < e then ent s₀.mem C w d else 0
  out : Outs B (selOut w) s₀.mem u.mem
  keep : Keep selERegs s₀ u

theorem selOut_fit {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) : ∀ r ∈ selOut w, r.1 + r.2 ≤ Z := by
  have := h.hZ
  intro r hr
  simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [slot] at *; omega

/-- The context's entries are kept by a change of `selOut`. -/
theorem ent_of_outs {s₀ u : State} {B C : Addr} {Z w a : Nat} (h : Env s₀ B Z w) (hc : CtxRd s₀ B Z C w)
    (ho : Outs B (selOut w) s₀.mem u.mem) (ha : a < 32) : ent u.mem C w a = ent s₀.mem C w a :=
  Outside.val32 (outs_ctx ho (selOut_fit h) hc.sep) (Or.inl (by have := row_fits (w := w) ha; omega))
    (by have := row_fits (w := w) ha; have := hc.hn; omega)

/-- Two entries of the selection. -/
theorem selPair_ok {s₀ u : State} {B C : Addr} {Z w d e : Nat} (h₀ : Env s₀ B Z w) (hc₀ : CtxRd s₀ B Z C w)
    (hi : SelI s₀ B C Z w d e u) (he : e + 2 ≤ 32) (hd : d < 32) :
    WP isa (.seq (selEntry 5 4) (.seq (selEntry 4 5) (.block [.subi .r3 .r25 32]))) u fun v =>
      SelI s₀ B C Z w d (e + 2) v ∧ v.gpr .r3 = BitVec.ofNat 64 (e + 2) - BitVec.ofNat 64 32 := by
  refine WP.seq (WP.mono (selEntry_ok (o := 5) (t := 4) hi.env hi.h30 hi.ctx hi.h25 hi.h26 (by omega) hd
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun u₁ ⟨⟨a5, j1, o1⟩, k1⟩ => ?_)
  have o1' := Outs.cover o1 (selEOut_cover w (Or.inr rfl))
  have ou1 := hi.out.trans o1'
  have e1 := hi.env.keep k1 (by decide)
  have c1 : CtxRd u₁ B Z C w := hi.ctx.congr k1.rd k1.wr
  refine WP.seq (WP.mono (selEntry_ok (o := 4) (t := 5) e1 ((k1.gpr .r30 (by decide)).trans hi.h30) c1 j1
    ((k1.gpr .r26 (by decide)).trans hi.h26) (by omega) hd
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun u₂ ⟨⟨a4, j2, o2⟩, k2⟩ => ?_)
  have o2' := Outs.cover o2 (selEOut_cover w (Or.inl rfl))
  have ou2 := ou1.trans o2'
  have e2 := e1.keep k2 (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 (e + 2) - BitVec.ofNat 64 32 ∧
      v.mem = u₂.mem) (by prun [j2]) (by decide)) fun v ⟨⟨a3, m3⟩, k3⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, a3⟩
  · exact e2.keep k3 (by decide)
  · exact (((k1.trans k2).trans k3).gpr .r30 (by decide)).trans hi.h30
  · exact c1.congr ((k2.trans k3).rd) ((k2.trans k3).wr)
  · rw [k3.gpr .r25 (by decide), j2]
  · exact (((k1.trans k2).trans k3).gpr .r26 (by decide)).trans hi.h26
  · rw [m3, a4, a5, hi.acc, ent_of_outs h₀ hc₀ ou1 (by omega), ent_of_outs h₀ hc₀ hi.out (by omega)]
    by_cases h1 : e + 1 = d
    · subst h1; simp
    · by_cases h0 : e = d
      · subst h0; simp
      · rw [ite_eq_right h1, ite_eq_right h0]
        by_cases hl : d < e
        · rw [ite_eq_left hl, ite_eq_left (by omega)]
        · rw [ite_eq_right hl, ite_eq_right (by omega)]
  · rw [m3]; exact ou2
  · exact ((hi.keep.trans k1).trans k2).trans k3 |>.mono (by decide)

/-- `select`: array 4 `:=` entry `d` (`r26`) of the context (`r30`). -/
theorem select_ok {s : State} {B C : Addr} {Z w d : Nat} (h : Env s B Z w) (h30 : s.gpr .r30 = C)
    (hc : CtxRd s B Z C w) (h26 : s.gpr .r26 = BitVec.ofNat 64 d) (hd : d < 32) :
    WP isa select s fun u =>
      (arr u.mem B w 4 = ent s.mem C w d ∧ Outs B (selOut w) s.mem u.mem) ∧ Keep selERegs s u := by
  have hZ := h.hZ
  have hnw := h.hs.nowrap
  have hw := h.hw; have hw' := h.hw'
  have ha4 := h.arr (show 4 < 28 by decide)
  unfold select
  refine WP.seq (WP.mono (h.base (rd := .r14) (by decide) (by decide) 4) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (h.hs.congr k1.wr) a14 ((k1.gpr .r11 (by decide)).trans h.h11)
    (by omega) (by omega) (by omega)) fun s₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  rw [m1] at o2
  have k12 := k1.trans k2
  have o2' : Outs B (selOut w) s.mem s₂.mem := Outs.of_outside (o2.mono (o' := slot w 3)
    (n' := 3 * (8 * (w + 2))) (by simp only [slot]; omega) (by simp only [slot]; omega)) (by simp [selOut])
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun v => v.gpr .r25 = BitVec.ofNat 64 0 ∧ v.mem = s₂.mem)
    (by prun) (by decide)) fun s₃ ⟨⟨a25, m3⟩, k3⟩ => ?_)
  have i0 : SelI s B C Z w d 0 s₃ := by
    refine ⟨(h.keep k12 (by decide)).keep k3 (by decide), ((k12.trans k3).gpr .r30 (by decide)).trans h30,
      hc.congr (k12.trans k3).rd (k12.trans k3).wr, a25, ((k12.trans k3).gpr .r26 (by decide)).trans h26,
      ?_, by rw [m3]; exact o2', (k12.trans k3).mono (by decide)⟩
    rw [ite_eq_right (by omega), arr, m3, ← wordsVal_eq_val32]
    exact wordsVal_zero' z2
  refine WP.loop (fun n v => 1 ≤ n ∧ n ≤ 16 ∧ SelI s B C Z w d (32 - 2 * n) v) (fun n v ⟨hn1, hn16, hv⟩ => ?_)
    16 s₃ ⟨by decide, by decide, i0⟩
  refine WP.mono (selPair_ok h hc hv (by omega) hd) fun v' ⟨hv', a3⟩ => ?_
  rw [VG.PPC64LE.eval_nonzero, a3, ofNat_sub_bne (by omega) (by decide)]
  by_cases hn : n = 1
  · subst hn
    refine .inl ⟨by simp, ?_⟩
    refine ⟨⟨?_, hv'.out⟩, hv'.keep⟩
    rw [hv'.acc, ite_eq_left (by omega)]
  · refine .inr ⟨by simp; omega, n - 1, by omega, by omega, by omega, ?_⟩
    rw [show 32 - 2 * (n - 1) = 32 - 2 * n + 2 by omega]; exact hv'

/-! ## The rows -/

/-- `g^E R mod p`, in Montgomery form. -/
abbrev combM (G P w E : Nat) : Nat := Spec.Rsa.powMod G E P * 2 ^ (64 * w) % P

/-- What the comb changes: arrays 1 to 7. -/
abbrev combOut (w : Nat) : List (Nat × Nat) := [(slot w 1, 7 * (8 * (w + 2)))]

theorem to_comb {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, slot w 1 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8) : Outs B (combOut w) m m' :=
  Outs.cover h fun r hr' => by
    have h' := hr r hr'
    exact ⟨_, List.mem_cons_self, h'.1, by simp only [slot] at h' ⊢; omega⟩

/-- What a row changes: arrays 2 to 6. -/
abbrev rowOut (w : Nat) : List (Nat × Nat) := [(slot w 2, 5 * (8 * (w + 2)))]

theorem to_row {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, slot w 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 7) : Outs B (rowOut w) m m' :=
  Outs.cover h fun r hr' => by
    have h' := hr r hr'
    exact ⟨_, List.mem_cons_self, h'.1, by simp only [slot] at h' ⊢; omega⟩

theorem row_comb {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (rowOut w) m m') : Outs B (combOut w) m m' :=
  to_comb h fun r hr => by
    simp only [rowOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩

theorem combOut_fit {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) : ∀ r ∈ combOut w, r.1 + r.2 ≤ Z := by
  have := h.hZ
  intro r hr
  simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [slot] at *; omega

/-- The header's words are kept by a change of arrays 1 to 7. -/
theorem hdr_of_comb {B : Addr} {w x : Nat} {m m' : Mem} (ho : Outs B (combOut w) m m') (hx : x + 8 ≤ 256) :
    m'.readW (off B x) 64 = m.readW (off B x) 64 :=
  ho.word (d := x) (fun r hr => by
    simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only [slot, hdrBytes]; omega) (by omega)

/-- A number apart from arrays 1 to 7 (array 0, or one from array 8). -/
theorem val_of_comb {B : Addr} {w j : Nat} {m m' : Mem} (ho : Outs B (combOut w) m m') (hj : j = 0)
    (hB : B.toNat + slot w 8 ≤ 2 ^ 64) : arr m' B w j = arr m B w j := by
  subst hj
  exact Outs.val32 ho (fun r hr => by
    simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only [slot]; omega) (by simp only [slot] at hB ⊢; omega)

/-- x's octets, apart from the working space, are kept. -/
theorem byte_of_outs {B X : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) {n : Nat} (hsep : ∀ y, ofs B y < Z → off X n ≠ y) : m' (off X n) = m (off X n) :=
  h _ fun r hr' => Or.inr (by
    have := hr r hr'
    by_cases hl : ofs B (off X n) < Z
    · exact absurd rfl (hsep _ hl)
    · omega)

/-- The registers a row writes. -/
def stepRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25, .r26]

/-- The comb with `n` rows left (`r24`), from `s₀`, the accumulator (array 6)
`A`; the rows in `r21`, x's address in `r27` and the context's in `r30`. -/
structure CS (s₀ : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits n A : Nat) (u : State) : Prop where
  env : Env u B Z w
  h28 : u.gpr .r28 = BitVec.ofNat 64 xb.length
  h12 : (u.gpr .r12).toNat < 2 ^ 32
  hinv : (w32 u.mem B (slot w 0) * (u.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  h30 : u.gpr .r30 = C
  ctx : CtxRd u B Z C w
  ents : ∀ a < 32, ent u.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  hp : arr u.mem B w 0 = P
  h24 : u.gpr .r24 = BitVec.ofNat 64 n
  h21 : u.gpr .r21 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  h27 : u.gpr .r27 = X
  xrd : ∀ n < xb.length, InRegions (u.rd ++ u.wr) (off X n) 1
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  xval : ∀ n (h : n < xb.length), u.mem (off X n) = xb[n]
  acc : arr u.mem B w 6 = A
  one : arr u.mem B w 7 = 1
  out : Outs B (combOut w) s₀.mem u.mem
  keep : Keep stepRegs s₀ u

theorem not_step_regs : ∀ r ∈ ([.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r30, .r31] : List Reg),
    r ∉ stepRegs := by decide

/-- `CS` after a change of `rowOut` that keeps registers that `CS` reads but
`r24`. -/
theorem CS.frame {s₀ u v : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n A n' A' : Nat}
    (h : CS s₀ B C X Z w xb P G bits n A u) {rs : List Reg} (ho' : Outs B (rowOut w) u.mem v.mem)
    (k : Keep rs u v) (hrs : ∀ r ∈ rs, r ∈ stepRegs := by decide)
    (h24 : v.gpr .r24 = BitVec.ofNat 64 n') (hacc : arr v.mem B w 6 = A') :
    CS s₀ B C X Z w xb P G bits n' A' v := by
  have ho := row_comb ho'
  have hfit := combOut_fit h.env
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have g : ∀ r ∈ ([.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r30, .r31] : List Reg), v.gpr r = u.gpr r :=
    fun r hr => k.gpr r fun h' => not_step_regs r hr (hrs r h')
  have hreg : ∀ r ∈ envRegs, r ∉ rs := fun r hr hr' => by
    have := hrs r hr'; simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [stepRegs] at this
  have hctx : Outside C (8 * ctxWords w) (2 ^ 64) u.mem v.mem := outs_ctx ho hfit h.ctx.sep
  have hapart : ∀ j, j = 0 ∨ j = 7 → arr v.mem B w j = arr u.mem B w j := fun j hj =>
    Outs.val32 ho' (fun r hr => by
      simp only [rowOut, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rcases hj with rfl | rfl <;> simp only [slot] <;> omega)
      (by rcases hj with rfl | rfl <;> simp only [slot] at hZ ⊢ <;> omega)
  refine ⟨h.env.keep k hreg, (g .r28 (by decide)).trans h.h28, by rw [g .r12 (by decide)]; exact h.h12,
    by
      rw [g .r12 (by decide), Pub.Outs.w32 ho (fun r hr => by
        simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)]
      exact h.hinv,
    (g .r30 (by decide)).trans h.h30, h.ctx.congr k.rd k.wr,
    fun a ha => by
      rw [← h.ents a ha]
      exact Outside.val32 hctx (Or.inl (by have := row_fits (w := w) ha; omega))
        (by have := row_fits (w := w) ha; have := h.ctx.hn; omega),
    by rw [hapart 0 (.inl rfl)]; exact h.hp, h24, (g .r21 (by decide)).trans h.h21, (g .r27 (by decide)).trans h.h27,
    fun n hn => by rw [k.rd, k.wr]; exact h.xrd n hn, h.xsep,
    fun n hn => by rw [byte_of_outs ho hfit (h.xsep n hn)]; exact h.xval n hn, hacc,
    by rw [hapart 7 (.inr rfl)]; exact h.one,
    h.out.trans ho, h.keep.trans k |>.mono (fun r hr => by
      simp only [List.mem_append] at hr; rcases hr with hr | hr
      · exact hr
      · exact hrs r hr)⟩

theorem combM_lt {G P w : Nat} (hP : 0 < P) (E : Nat) : combM G P w E < P := Nat.mod_lt _ hP

theorem combDigit_eq (bits x i : Nat) :
    combDigit x i (Spec.Rsa.FixedBaseComb.rows bits) = Rsa.FixedBaseComb.digit bits x i := rfl

/-- What a row needs besides `CS`. -/
structure RowP (P bits : Nat) (xb : List Byte) : Prop where
  odd : P % 2 = 1
  one : 1 < P
  rows : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639
  len : 8 * xb.length < 2 ^ 31

/-- `montOp o a b` in the comb's state: array `o :=` the Montgomery product. -/
theorem CS.mont {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n A : Nat}
    (h : CS s₀ B C X Z w xb P G bits n A u) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2)
    (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : arr u.mem B w b < P) :
    WP isa (PublicChecked.montOp o a b) u fun v =>
      (arr v.mem B w o < P ∧ arr v.mem B w o * 2 ^ (64 * w) % P = arr u.mem B w a * arr u.mem B w b % P ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] u.mem v.mem) ∧
      Keep Pub.montRegs u v := by
  have := h.env.hw; have := h.env.hw'; have hZ := h.env.hZ
  refine WP.mono (Pub.montOp_ok h.env.hs ho ha hb ho2 ho3 ha2 hb2 (by omega) (by omega)
    (Nat.le_trans (by simp only [slot]; omega) hZ) h.env.h10 h.env.h29 h.env.h11 h.h12 h.hinv
    (by rw [← arr, ← arr, h.hp]; exact hB)) fun v ⟨⟨lt, eq, out⟩, k⟩ => ⟨⟨?_, ?_, out⟩, k⟩
  · rw [arr, ← h.hp]; exact lt
  · rw [arr, ← h.hp]; exact eq

theorem slot_row (w o : Nat) (ho : o = 4 ∨ o = 6) :
    ∀ r ∈ [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))],
      slot w 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 7 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> (try rcases ho with rfl | rfl) <;> omega

/-- One row: from `n + 1` rows left to `n`. -/
theorem step_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n : Nat} (hq : RowP P bits xb)
    (h : CS s₀ B C X Z w xb P G bits (n + 1) (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (n + 1))) u)
    (hn : n < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa step u fun v =>
      CS s₀ B C X Z w xb P G bits n (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) n)) v := by
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hP : 0 < P := by have := hq.one; omega
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h1 := hq.rows
  generalize hx : Spec.Rsa.os2ip xb = x at h ⊢
  unfold step
  simp only [seqs]
  -- The square.
  refine WP.seq (WP.mono (h.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.acc]; exact combM_lt hP _)) fun u₁ ⟨⟨lt1, eq1, o1⟩, k1⟩ => ?_)
  rw [h.acc] at eq1
  have a1 := Rsa.FixedBaseComb.mont_square_encoded cop lt1 rfl eq1
  have c1 := h.frame (to_row o1 (slot_row w 6 (.inr rfl))) k1 (by decide)
    (by rw [k1.gpr .r24 (by decide)]; exact h.h24) a1
  -- The digit.
  have xc : XCtx u₁ X xb n (Spec.Rsa.FixedBaseComb.rows bits) := ⟨c1.h28, c1.h24, c1.h21, c1.h27,
    c1.xrd, c1.xval, by omega, hq.len⟩
  refine WP.seq (WP.mono (digit_ok xc) fun u₂ ⟨⟨a26, m2⟩, k2⟩ => ?_)
  rw [hx, combDigit_eq] at a26
  have hd := Rsa.FixedBaseComb.digit_lt bits x n
  have c2 := c1.frame (A' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1)))
    (by rw [m2]; exact Outs.refl _ _ _) k2 (by decide) (by rw [k2.gpr .r24 (by decide)]; exact c1.h24)
    (by rw [m2]; exact c1.acc)
  -- The entry.
  refine WP.seq (WP.mono (select_ok c2.env c2.h30 c2.ctx a26 hd) fun u₃ ⟨⟨a3, o3⟩, k3⟩ => ?_)
  rw [c2.ents _ hd] at a3
  have o3' : Outs B (rowOut w) u₂.mem u₃.mem := to_row o3 (fun r hr => by
    simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩)
  have c3 := c2.frame (A' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1))) o3' k3 (by decide)
    (by rw [k3.gpr .r24 (by decide)]; exact c2.h24) (by
    rw [arr, Outs.val32 o3 (fun r hr => by
      simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)]
    exact c2.acc)
  -- The product.
  refine WP.seq (WP.mono (c3.mont (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [a3]; exact combM_lt hP _)) fun u₄ ⟨⟨lt4, eq4, o4⟩, k4⟩ => ?_)
  rw [c3.acc, a3] at eq4
  have a4 := Rsa.FixedBaseComb.mont_product_encoded cop lt4 rfl rfl eq4
  rw [← Rsa.FixedBaseComb.high_step bits x n hn] at a4
  have c4 := c3.frame (to_row o4 (slot_row w 6 (.inr rfl))) k4 (by decide)
    (by rw [k4.gpr .r24 (by decide)]; exact c3.h24) a4
  -- `n` rows left.
  refine WP.mono (WP.keep [.r24] (Q := fun v => v.gpr .r24 = BitVec.ofNat 64 n ∧ v.mem = u₄.mem) (by
    prun [c4.h24, ofNat_sub_one (show 1 ≤ n + 1 by omega) (show n + 1 < 2 ^ 64 by omega), Nat.add_sub_cancel])
    (by decide)) fun v ⟨⟨a5, m5⟩, k5⟩ => ?_
  exact c4.frame (by rw [m5]; exact Outs.refl _ _ _) k5 (by decide) a5 (by rw [m5]; exact c4.acc)

/-! ## The comb -/

/-- What the comb needs: the working space with p in array 0, the context
(its address in the header) and its entries, x's octets (their address in the
header) and the header's row count. -/
structure CombIn (s : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits : Nat) : Prop where
  env : Env s B Z w
  h23 : s.gpr .r23 = B
  h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length
  hC : s.mem.readW (off B hCtx) 64 = C
  ctx : CtxRd s B Z C w
  ents : ∀ a < 32, ent s.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  r2 : val32 s.mem C (rowOff w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % P
  hp : arr s.mem B w 0 = P
  hRw : s.mem.readW (off B hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  hX : s.mem.readW (off B 64) 64 = X
  xrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  xval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  row : RowP P bits xb
  pos : 0 < bits

/-- The registers the comb writes. -/
def combRegs : List Reg := .r12 :: .r21 :: .r27 :: .r30 :: stepRegs

theorem row1_fits (w : Nat) : rowOff w 1 + 8 * w ≤ 8 * ctxWords w := by unfold rowOff ctxWords; omega

/-- The rows, from `n` left, by `wp_countdown` on `r24`. -/
theorem rows_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat} (hq : RowP P bits xb)
    (h : CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) u)
    (hpos : 0 < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa (.loop step (.nonzero .d .r24)) u
      (CS s₀ B C X Z w xb P G bits 0 (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0))) := by
  have h1 := hq.rows
  refine WP.mono (wp_countdown (body := step) (cnt := .r24) (N := Spec.Rsa.FixedBaseComb.rows bits) (by omega) hpos
    (fun i v => CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits - i)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits - i))) v)
    (fun i hi v hv hc => ?_) (by simpa using h) h.h24) fun v hv => by simpa using hv
  have e : Spec.Rsa.FixedBaseComb.rows bits - i = Spec.Rsa.FixedBaseComb.rows bits - (i + 1) + 1 := by omega
  rw [e] at hv hc
  refine WP.mono (step_ok hq hv (by omega)) fun v' hv' => ⟨hv', ?_⟩
  rw [hv'.h24, hc, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]

/-- The comb's first block: the context, x's address, the rows, and `r3 := 1`. -/
abbrev headBlock : List Instr := [ldh .r30 hCtx, .load .d .r27 .r23 64, ldh .r21 hRows, .li .r3 1]

/-- The comb after its first block. -/
abbrev combRest : Prog isa := seqs [loadRow 1, .block PublicChecked.minv, PublicChecked.one,
  PublicChecked.montOp 6 1 7, .block [.addi .r24 .r21 0], .loop step (.nonzero .d .r24), PublicChecked.montOp 4 6 7]

theorem comb_eq : comb = .seq (.block headBlock) combRest := rfl

theorem head_ok {s : State} {B C X : Addr} {Z bits : Nat} (hs : Scr s B Z) (hZ : 72 ≤ Z) (h23 : s.gpr .r23 = B)
    (hC : s.mem.readW (off B hCtx) 64 = C) (hX : s.mem.readW (off B 64) 64 = X)
    (hRw : s.mem.readW (off B hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) :
    WP isa (.block headBlock) s fun u => (u.gpr .r30 = C ∧ u.gpr .r27 = X ∧
      u.gpr .r21 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧ u.gpr .r3 = BitVec.ofNat 64 1 ∧
      u.mem = s.mem) ∧ Keep [.r3, .r21, .r27, .r30] s u := by
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 0) 8 := by
    rw [h23]; exact hs.ld (d := 0) (n := 8) (by omega)
  have l64 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 64) 8 := by
    rw [h23]; exact hs.ld (d := 64) (n := 8) (by omega)
  have l24 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 24) 8 := by
    rw [h23]; exact hs.ld (d := 24) (n := 8) (by omega)
  have v0 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 0) 64 = C := by rw [h23]; exact hC
  have v64 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 64) 64 = X := by rw [h23]; exact hX
  have v24 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 24) 64 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) := by rw [h23]; exact hRw
  refine WP.keep [.r3, .r21, .r27, .r30] ?_ (by decide)
  unfold headBlock ldh
  prun [hCtx, hRows, l0, l64, l24, v0, v64, v24]

theorem comb_ok {s : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) :
    WP isa comb s fun t =>
      (arr t.mem B w 4 = Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
        arr t.mem B w 0 = P ∧ Outs B (combOut w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep combRegs s t := by
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hw := h.env.hw; have hw' := h.env.hw'
  have hq := h.row
  have hP : 0 < P := by have := hq.one; omega
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have hfit := combOut_fit h.env
  have hB8 : B.toNat + slot w 8 ≤ 2 ^ 64 := by simp only [slot] at hZ ⊢; omega
  rw [comb_eq]
  simp only [combRest, seqs]
  -- The context, x's address, the rows, and `r3 := 1`.
  refine WP.seq (WP.mono (head_ok h.env.hs (by simp only [slot] at hZ; omega) h.h23 h.hC h.hX h.hRw)
    fun s₁ ⟨⟨a30, a27, a21, a3, m1⟩, k1⟩ => ?_)
  have e1 := h.env.keep k1 (by decide)
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (loadRow_ok (a := 1) (j := 1) (Zc := 8 * ctxWords w) e1 a30
    a3 (by decide) (by decide) (row1_fits w) h.ctx.hn
    (fun i hi => by rw [k1.rd, k1.wr]; exact h.ctx.rd _ (by have := row1_fits w; omega)) h.ctx.sep)
    fun s₂ ⟨⟨w2, o2⟩, k2⟩ => ?_)
  rw [m1] at w2 o2
  have k12 := k1.trans k2
  have e2 := e1.keep k2 (by decide)
  have r1 : arr s₂.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by rw [arr, val32_of_words w2]; exact h.r2
  have p2 : arr s₂.mem B w 0 = P := by
    rw [arr, Outside.val32 o2 (by simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)]; exact h.hp
  -- `-p⁻¹ mod 2³²`.
  have hlow : (word s₂.mem B (slot w 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₂.mem B (slot w 0)
    have h2 : val32 s₂.mem B (slot w 0) (2 * w - 1 + 1) =
        w32 s₂.mem B (slot w 0) + 2 ^ 32 * val32 s₂.mem B (slot w 0 + 4) (2 * w - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * w)] at h2
    have := hq.odd
    rw [arr] at p2
    omega
  refine WP.seq (WP.mono (Pub.minv_ok e2.hs e2.h10 (by simp only [slot] at hZ ⊢; omega) hlow)
    fun s₃ ⟨⟨r12lt, r12inv, m3⟩, k3⟩ => ?_)
  have e3 := e2.keep k3 (by decide)
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok e3.hs (by omega) (by omega) (Nat.le_trans (by simp only [slot]; omega) hZ)
    e3.h10 e3.h29 e3.h11) fun s₄ ⟨⟨one4, o4⟩, k4⟩ => ?_)
  rw [m3] at o4
  have e4 := e3.keep k4 (by decide)
  have k14 := (k12.trans k3).trans k4
  have p4 : arr s₄.mem B w 0 = P := by
    rw [arr, Outside.val32 o4 (by simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)]; exact p2
  have r4 : arr s₄.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    rw [arr, Outside.val32 o4 (by simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)]; exact r1
  have w4 : w32 s₄.mem B (slot w 0) = w32 s₂.mem B (slot w 0) := by
    exact Outside.w32 o4 (by simp only [slot]; omega) (by simp only [slot] at hZ ⊢; omega)
  have g12 : s₄.gpr .r12 = s₃.gpr .r12 := k4.gpr .r12 (by decide)
  -- Montgomery one in array 6.
  refine WP.seq (WP.mono (Pub.montOp_ok e4.hs (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (Nat.le_trans (by simp only [slot]; omega) hZ)
    e4.h10 e4.h29 e4.h11 (by rw [g12]; exact r12lt) (by rw [g12, w4]; exact r12inv)
    (by rw [one4, ← arr, p4]; exact hq.one)) fun s₅ ⟨⟨lt5, eq5, o5⟩, k5⟩ => ?_)
  rw [← arr, ← arr, p4] at lt5
  rw [one4, ← arr, ← arr, ← arr, p4, r4] at eq5
  have a5 : arr s₅.mem B w 6 = combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb)
      (Spec.Rsa.FixedBaseComb.rows bits)) := by
    rw [Rsa.FixedBaseComb.high_top, combM, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hq.one, Nat.one_mul]
    rw [← Nat.mod_eq_of_lt lt5]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq5, Nat.mul_one, Nat.mod_mod])
  have k15 := k14.trans k5
  have k25 := ((k2.trans k3).trans k4).trans k5
  have e5 := e4.keep k5 (by decide)
  have o15 : Outs B (combOut w) s.mem s₅.mem := by
    have h1 : Outs B (combOut w) s.mem s₂.mem := to_comb (Outs.of_outside (rs := [(slot w 1, 8 * w)]) o2 (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr; subst hr
          exact ⟨Nat.le_refl _, by simp only [slot]; omega⟩)
    have h2 : Outs B (combOut w) s₂.mem s₄.mem := to_comb (Outs.of_outside (rs := [(slot w 7, 8 * w)]) o4 (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr; subst hr
          exact ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩)
    have h3 : Outs B (combOut w) s₄.mem s₅.mem := row_comb (to_row o5 (slot_row w 6 (.inr rfl)))
    exact (h1.trans h2).trans h3
  have p5 : arr s₅.mem B w 0 = P := by
    rw [arr, Outs.val32 o5 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot] at hZ ⊢; omega)]; exact p4
  have one5 : arr s₅.mem B w 7 = 1 := by
    rw [arr, Outs.val32 o5 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot] at hZ ⊢; omega)]; exact one4
  -- `rows` rows left.
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun v => v.gpr .r24 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      v.mem = s₅.mem) (by prun [(k25.gpr .r21 (by decide)).trans a21, BitVec.add_zero]) (by decide)) fun s₆ ⟨⟨a6, m6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hpos := Rsa.FixedBaseComb.rows_pos h.pos
  have c6 : CS s₆ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) s₆ := by
    have hctx : Outside C (8 * ctxWords w) (2 ^ 64) s.mem s₆.mem := outs_ctx (by rw [m6]; exact o15) hfit h.ctx.sep
    refine ⟨e5.keep k6 (by decide), (k16.gpr .r28 (by decide)).trans h.h28,
      by rw [k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), g12]; exact r12lt,
      by
        rw [k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), g12, m6,
          Pub.Outs.w32 o5 (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot] at hZ ⊢; omega), w4]
        exact r12inv,
      ((k25.trans k6).gpr .r30 (by decide)).trans a30, h.ctx.congr k16.rd k16.wr,
      fun a ha => by
        rw [← h.ents a ha]
        exact Outside.val32 hctx (Or.inl (by have := row_fits (w := w) ha; omega))
          (by have := row_fits (w := w) ha; have := h.ctx.hn; omega),
      by rw [m6]; exact p5, a6, ((k25.trans k6).gpr .r21 (by decide)).trans a21,
      ((k25.trans k6).gpr .r27 (by decide)).trans a27,
      fun n hn => by rw [k16.rd, k16.wr]; exact h.xrd n hn, h.xsep,
      fun n hn => by rw [m6, byte_of_outs o15 hfit (h.xsep n hn)]; exact h.xval n hn,
      by rw [m6]; exact a5, by rw [m6]; exact one5, Outs.refl _ _ _, Keep.refl _ _⟩
  -- The rows.
  refine WP.seq (WP.mono (rows_ok hq c6 hpos) fun v hv => ?_)
  -- Out of Montgomery form.
  refine WP.mono (hv.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hv.one]; exact hq.one)) fun t ⟨⟨lt7, eq7, o7⟩, k7⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hv.acc, hv.one, Nat.mul_one, Nat.mod_mod] at eq7
    rw [← Nat.mod_eq_of_lt lt7, ← Nat.mod_eq_of_lt (show Spec.Rsa.powMod G _ P < P from by
      rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP)]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq7, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod])
  · rw [arr, Outs.val32 o7 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot] at hZ ⊢; omega)]; exact hv.hp
  · exact ((by rw [m6]; exact o15 : Outs B (combOut w) s.mem s₆.mem).trans hv.out).trans
      (row_comb (to_row o7 (slot_row w 4 (.inl rfl))))
  · exact (k7.gpr .r10 (by decide)).trans hv.env.h10
  · exact ((k16.trans hv.keep).trans k7).mono (by decide)

end VG.Proof.Ffdh.PPC64LE.Cached
