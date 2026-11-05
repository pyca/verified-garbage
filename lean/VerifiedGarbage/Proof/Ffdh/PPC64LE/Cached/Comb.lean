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
open VG.Proof.MillerRabin.PPC64LE (Env sel_ok selRegs arr)
open VG.Proof.Bignum (slot slot_sep)

/-- The context's words. -/
abbrev ctxWords (w : Nat) : Nat := 3 + 34 * w

/-- The context at `C`: readable, apart from the working space, its address
in the header. -/
structure CtxRd (s : State) (B : Addr) (Z : Nat) (C : Addr) (w : Nat) : Prop where
  hC : s.mem.readW (off B hCtx) 64 = C
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
    (hC : t.mem.readW (off B hCtx) 64 = C) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxRd t B Z C w :=
  ⟨hC, h.hn, fun d hd => by rw [hrd, hwr]; exact h.rd d hd, h.sep⟩

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
def selERegs : List Reg := [.r0, .r3, .r4, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- What `selEntry` changes. -/
abbrev selEOut (w o : Nat) : List (Nat × Nat) := [(hJ, 8), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))]

/-- `selEntry o t`: entry `e` (the header's `hJ`) to array `o` if it is the
digit `d` (the header's `hD`), else array `t`; `e` advanced. -/
theorem selEntry_ok {s : State} {B C : Addr} {Z w e d o t : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (hc : CtxRd s B Z C w) (hJw : s.mem.readW (off B hJ) 64 = BitVec.ofNat 64 e)
    (hDw : s.mem.readW (off B hD) 64 = BitVec.ofNat 64 d) (he : e < 32) (hd : d < 32)
    (ho : o < 28) (ht : t < 28) (ho3 : o ≠ 3) (ht3 : t ≠ 3) (hot : o ≠ t) :
    WP isa (selEntry o t) s fun u =>
      (arr u.mem B w o = (if e = d then ent s.mem C w e else arr s.mem B w t) ∧
        u.mem.readW (off B hJ) 64 = BitVec.ofNat 64 (e + 1) ∧ Outs B (selEOut w o) s.mem u.mem) ∧
      Keep selERegs s u := by
  have hw := h.hw; have hw' := h.hw'; have hZ := h.hZ
  have hnw := h.hs.nowrap
  have haO := h.arr ho; have haT := h.arr ht; have ha3 := h.arr (show 3 < 28 by decide)
  unfold selEntry
  -- `r3 := e + 2`.
  have l48 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [h23]; exact h.hs.ld (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have v48 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 e := by rw [h23]; exact hJw
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (e + 2) ∧ u.mem = s.mem)
    (by unfold ldh; prun [hJ, l48, v48, ofNat_add']) (by decide)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  refine WP.seq (WP.mono (loadRow_ok (a := 3) (Zc := 8 * ctxWords w) e1 ((k1.gpr .r23 (by decide)).trans h23)
    (by rw [m1]; exact hc.hC) a3 (by decide) (by omega) (row_fits he) hc.hn
    (fun i hi => by rw [k1.rd, k1.wr]; exact hc.rd _ (by have := row_fits (w := w) he; unfold rowOff ctxWords at *; omega)) hc.sep)
    fun s₂ ⟨⟨w2, o2⟩, k2⟩ => ?_)
  rw [m1] at w2 o2
  have k12 := k1.trans k2
  have e2 := e1.keep k2 (by decide)
  have hw2 : ∀ x, x + 8 ≤ 256 → word s₂.mem B x = word s.mem B x := fun x hx =>
    o2.word (Or.inl (by unfold slot hdrBytes; omega)) (by omega)
  have h23₂ : s₂.gpr .r23 = B := (k12.gpr .r23 (by decide)).trans h23
  -- The mask of `e = d`.
  have l48' : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [h23₂, k12.rd, k12.wr]; exact h.hs.ld (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have v48' : s₂.mem.readW (s₂.gpr .r23 + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 e := by
    rw [h23₂]; exact (hw2 48 (by omega)).trans hJw
  have l40 : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r23 + BitVec.ofNat 64 40) 8 := by
    rw [h23₂, k12.rd, k12.wr]; exact h.hs.ld (d := 40) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have v40 : s₂.mem.readW (s₂.gpr .r23 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 d := by
    rw [h23₂]; exact (hw2 40 (by omega)).trans hDw
  refine WP.seq (WP.mono (WP.keep [.r0, .r4, .r20] (Q := fun u =>
      u.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if decide (e = d) then 1 else 0) ∧ u.mem = s₂.mem)
    (by unfold ldh; prun [hJ, hD, l48', v48', l40, v40, GenerateKey.eq_mask (show e < 2 ^ 32 by omega) (show d < 2 ^ 32 by omega)])
    (by decide)) fun s₃ ⟨⟨a20, m3⟩, k3⟩ => ?_)
  have e3 := e2.keep k3 (by decide)
  refine WP.seq (WP.mono (sel_ok e3 ho (by decide : 3 < 28) ht ho3 hot a20) fun s₄ ⟨⟨v4, o4⟩, k4⟩ => ?_)
  rw [m3] at v4 o4
  have k14 := (k12.trans k3).trans k4
  have hw4 : ∀ x, x + 8 ≤ 256 → word s₄.mem B x = word s.mem B x := fun x hx =>
    (o4.word (Or.inl (by unfold slot hdrBytes; omega)) (by omega)).trans (hw2 x hx)
  have h23₄ : s₄.gpr .r23 = B := (k14.gpr .r23 (by decide)).trans h23
  have l48'' : InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [h23₄, k14.rd, k14.wr]; exact h.hs.ld (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have s48 : InRegions s₄.wr (s₄.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [h23₄, k14.wr]; exact h.hs.st (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have v48'' : s₄.mem.readW (s₄.gpr .r23 + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 e := by
    rw [h23₄]; exact (hw4 48 (by omega)).trans hJw
  refine WP.mono (WP.keep [.r3] (Q := fun u =>
      u.mem = s₄.mem.writeW (off B 48) (BitVec.ofNat 64 (e + 1))) (by
    unfold ldh sth; prun [hJ, l48'', v48'', s48, ofNat_add']; rw [h23₄]) (by decide)) fun u ⟨um, uk⟩ => ⟨⟨?_, ?_, ?_⟩,
      (k14.trans uk).mono (by decide)⟩
  · have hu : arr u.mem B w o = arr s₄.mem B w o := by
      rw [um, arr, Outside.val32 (writeW_outside _ B (d := 48) _ (by omega)) (Or.inr (by unfold slot hdrBytes; omega))
        (by omega)]
    simp only [arr] at hu ⊢
    rw [hu, v4]
    by_cases hb : e = d
    · subst hb
      simp only [decide_true, ↓reduceIte]
      exact val32_of_words w2
    · simp only [hb, decide_false, ↓reduceIte, Bool.false_eq_true]
      exact Outside.val32 o2 (by have := slot_sep (w := w) ht3; omega) (by omega)
  · rw [um]; exact Mem.readW_writeW_self64 _ _ _
  · have o2' : Outs B (selEOut w o) s.mem s₂.mem :=
      Outs.of_outside (o2.mono (o' := slot w 3) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [selEOut])
    have o4' : Outs B (selEOut w o) s₂.mem s₄.mem := Outs.of_outside o4 (by simp [selEOut])
    have ou : Outs B (selEOut w o) s₄.mem u.mem := by
      rw [um]; exact Outs.of_outside (writeW_outside _ B (d := 48) _ (by omega)) (by simp [selEOut, hJ])
    exact (o2'.trans o4').trans ou

/-- What `select` changes: `hJ` and arrays 3 to 5. -/
abbrev selOut (w : Nat) : List (Nat × Nat) := [(hJ, 8), (slot w 3, 3 * (8 * (w + 2)))]

theorem selEOut_cover (w : Nat) {o : Nat} (ho : o = 4 ∨ o = 5) :
    ∀ r ∈ selEOut w o, ∃ R ∈ selOut w, R.1 ≤ r.1 ∧ r.1 + r.2 ≤ R.1 + R.2 := by
  intro r hr
  simp only [selEOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by simp only; omega⟩
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;> simp only [slot] <;> rcases ho with rfl | rfl <;> omega

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
  h23 : u.gpr .r23 = B
  ctx : CtxRd u B Z C w
  hJw : u.mem.readW (off B hJ) 64 = BitVec.ofNat 64 e
  hDw : u.mem.readW (off B hD) 64 = BitVec.ofNat 64 d
  acc : arr u.mem B w 4 = if d < e then ent s₀.mem C w d else 0
  out : Outs B (selOut w) s₀.mem u.mem
  keep : Keep selERegs s₀ u

theorem selOut_fit {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) : ∀ r ∈ selOut w, r.1 + r.2 ≤ Z := by
  have := h.hZ
  intro r hr
  simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [slot, hdrBytes, hJ] at * <;> omega

/-- The context's entries are kept by a change of `selOut`. -/
theorem ent_of_outs {s₀ u : State} {B C : Addr} {Z w a : Nat} (h : Env s₀ B Z w) (hc : CtxRd s₀ B Z C w)
    (ho : Outs B (selOut w) s₀.mem u.mem) (ha : a < 32) : ent u.mem C w a = ent s₀.mem C w a :=
  Outside.val32 (outs_ctx ho (selOut_fit h) hc.sep) (Or.inl (by have := row_fits (w := w) ha; omega))
    (by have := row_fits (w := w) ha; have := hc.hn; omega)

theorem hdr_of_outs {B : Addr} {w x : Nat} {m m' : Mem} (ho : Outs B (selOut w) m m') (hx : x + 8 ≤ 48) : m'.readW (off B x) 64 = m.readW (off B x) 64 :=
  ho.word (d := x) (fun r hr => by
    simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [slot, hdrBytes, hJ] <;> omega) (by omega)

/-- Two entries of the selection. -/
theorem selPair_ok {s₀ u : State} {B C : Addr} {Z w d e : Nat} (h₀ : Env s₀ B Z w) (hc₀ : CtxRd s₀ B Z C w)
    (hi : SelI s₀ B C Z w d e u) (he : e + 2 ≤ 32) (hd : d < 32) :
    WP isa (.seq (selEntry 5 4) (.seq (selEntry 4 5) (.block [ldh .r3 hJ, .subi .r3 .r3 32]))) u fun v =>
      SelI s₀ B C Z w d (e + 2) v ∧ v.gpr .r3 = BitVec.ofNat 64 (e + 2) - BitVec.ofNat 64 32 := by
  have hZ := h₀.hZ
  have hnw := h₀.hs.nowrap
  refine WP.seq (WP.mono (selEntry_ok (o := 5) (t := 4) hi.env hi.h23 hi.ctx hi.hJw hi.hDw (by omega) hd
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun u₁ ⟨⟨a5, j1, o1⟩, k1⟩ => ?_)
  have o1' := Outs.cover o1 (selEOut_cover w (Or.inr rfl))
  have ou1 := hi.out.trans o1'
  have e1 := hi.env.keep k1 (by decide)
  have g23 : u₁.gpr .r23 = B := (k1.gpr .r23 (by decide)).trans hi.h23
  have c1 : CtxRd u₁ B Z C w := hi.ctx.congr (by rw [hdr_of_outs o1' (by decide)]; exact hi.ctx.hC) k1.rd k1.wr
  have d1 : u₁.mem.readW (off B hD) 64 = BitVec.ofNat 64 d := by rw [hdr_of_outs o1' (by decide)]; exact hi.hDw
  refine WP.seq (WP.mono (selEntry_ok (o := 4) (t := 5) e1 g23 c1 j1 d1 (by omega) hd
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun u₂ ⟨⟨a4, j2, o2⟩, k2⟩ => ?_)
  have o2' := Outs.cover o2 (selEOut_cover w (Or.inl rfl))
  have ou2 := ou1.trans o2'
  have e2 := e1.keep k2 (by decide)
  have g23₂ : u₂.gpr .r23 = B := (k2.gpr .r23 (by decide)).trans g23
  have l48 : InRegions (u₂.rd ++ u₂.wr) (u₂.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [g23₂]; exact e2.hs.ld (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  have v48 : u₂.mem.readW (u₂.gpr .r23 + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (e + 1 + 1) := by
    rw [g23₂]; exact j2
  refine WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 (e + 2) - BitVec.ofNat 64 32 ∧
      v.mem = u₂.mem) (by unfold ldh; prun [hJ, l48, v48]) (by decide)) fun v ⟨⟨a3, m3⟩, k3⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, a3⟩
  · exact e2.keep k3 (by decide)
  · exact (k3.gpr .r23 (by decide)).trans g23₂
  · exact c1.congr (by rw [m3, hdr_of_outs o2' (by decide)]; exact c1.hC) ((k2.trans k3).rd) ((k2.trans k3).wr)
  · rw [m3]; exact j2
  · rw [m3, hdr_of_outs o2' (by decide)]; exact d1
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

/-- `select`: array 4 `:=` entry `d` (the header's `hD`) of the context. -/
theorem select_ok {s : State} {B C : Addr} {Z w d : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (hc : CtxRd s B Z C w) (hDw : s.mem.readW (off B hD) 64 = BitVec.ofNat 64 d) (hd : d < 32) :
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
  have g23 : s₂.gpr .r23 = B := (k12.gpr .r23 (by decide)).trans h23
  have o2' : Outs B (selOut w) s.mem s₂.mem := Outs.of_outside (o2.mono (o' := slot w 3)
    (n' := 3 * (8 * (w + 2))) (by simp only [slot]; omega) (by simp only [slot]; omega)) (by simp [selOut])
  have s48 : InRegions s₂.wr (s₂.gpr .r23 + BitVec.ofNat 64 48) 8 := by
    rw [g23]; exact (h.hs.congr k12.wr).st (d := 48) (n := 8) (by unfold slot hdrBytes at hZ; omega)
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.mem = s₂.mem.writeW (off B 48) (BitVec.ofNat 64 0))
    (by unfold sth; prun [hJ, s48]; rw [g23]) (by decide)) fun s₃ ⟨m3, k3⟩ => ?_)
  have o3 : Outs B (selOut w) s₂.mem s₃.mem := by
    rw [m3]; exact Outs.of_outside (writeW_outside _ B (d := 48) _ (by omega)) (by simp [selOut, hJ])
  have i0 : SelI s B C Z w d 0 s₃ := by
    refine ⟨(h.keep k12 (by decide)).keep k3 (by decide), (k3.gpr .r23 (by decide)).trans g23,
      hc.congr (by rw [hdr_of_outs (o2'.trans o3) (by decide)]; exact hc.hC) (k12.trans k3).rd (k12.trans k3).wr,
      by rw [m3]; exact Mem.readW_writeW_self64 _ _ _, by rw [hdr_of_outs (o2'.trans o3) (by decide)]; exact hDw,
      ?_, o2'.trans o3, (k12.trans k3).mono (by decide)⟩
    rw [ite_eq_right (by omega), arr, m3, Outside.val32 (writeW_outside _ B (d := 48) _ (by omega))
      (Or.inr (by unfold slot hdrBytes; omega)) (by omega)]
    rw [← wordsVal_eq_val32]
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

end VG.Proof.Ffdh.PPC64LE.Cached
