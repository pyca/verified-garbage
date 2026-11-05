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

/-! ## The rows -/

/-- `g^E R mod p`, in Montgomery form. -/
abbrev combM (G P w E : Nat) : Nat := Spec.Rsa.powMod G E P * 2 ^ (64 * w) % P

/-- What the comb changes: the header's `hI`, `hD` and `hJ`, and arrays 1 to 7. -/
abbrev combOut (w : Nat) : List (Nat × Nat) := [(32, 24), (slot w 1, 7 * (8 * (w + 2)))]

theorem to_comb {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, (32 ≤ r.1 ∧ r.1 + r.2 ≤ 56) ∨ (slot w 1 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8)) :
    Outs B (combOut w) m m' :=
  Outs.cover h fun r hr' => by
    rcases hr r hr' with h' | h'
    · exact ⟨_, List.mem_cons_self, h'.1, by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h'.1, by simp only [slot] at h' ⊢; omega⟩

/-- What a row changes: the header's `hI`, `hD` and `hJ`, and arrays 2 to 6. -/
abbrev rowOut (w : Nat) : List (Nat × Nat) := [(32, 24), (slot w 2, 5 * (8 * (w + 2)))]

theorem to_row {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, (32 ≤ r.1 ∧ r.1 + r.2 ≤ 56) ∨ (slot w 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 7)) :
    Outs B (rowOut w) m m' :=
  Outs.cover h fun r hr' => by
    rcases hr r hr' with h' | h'
    · exact ⟨_, List.mem_cons_self, h'.1, by simp only; omega⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h'.1, by simp only [slot] at h' ⊢; omega⟩

theorem row_comb {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (rowOut w) m m') : Outs B (combOut w) m m' :=
  to_comb h fun r hr => by
    simp only [rowOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨by decide, by decide⟩
    · exact .inr ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩

theorem combOut_fit {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) : ∀ r ∈ combOut w, r.1 + r.2 ≤ Z := by
  have := h.hZ
  intro r hr
  simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] at * <;> omega

theorem hdr_of_comb {B : Addr} {w x : Nat} {m m' : Mem} (ho : Outs B (combOut w) m m') (hx : x + 8 ≤ 32 ∨ 56 ≤ x)
    (hx' : x + 8 ≤ 256) : m'.readW (off B x) 64 = m.readW (off B x) 64 :=
  ho.word (d := x) (fun r hr => by
    simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by omega)

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
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- The comb with `n` rows left, from `s₀`, the accumulator (array 6) `A`. -/
structure CS (s₀ : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits n A : Nat) (u : State) : Prop where
  env : Env u B Z w
  h23 : u.gpr .r23 = B
  h28 : u.gpr .r28 = BitVec.ofNat 64 xb.length
  h12 : (u.gpr .r12).toNat < 2 ^ 32
  hinv : (w32 u.mem B (slot w 0) * (u.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  ctx : CtxRd u B Z C w
  ents : ∀ a < 32, ent u.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  hp : arr u.mem B w 0 = P
  hIw : u.mem.readW (off B hI) 64 = BitVec.ofNat 64 n
  hRw : u.mem.readW (off B hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  hX : u.mem.readW (off B 64) 64 = X
  xrd : ∀ n < xb.length, InRegions (u.rd ++ u.wr) (off X n) 1
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  xval : ∀ n (h : n < xb.length), u.mem (off X n) = xb[n]
  acc : arr u.mem B w 6 = A
  one : arr u.mem B w 7 = 1
  out : Outs B (combOut w) s₀.mem u.mem
  keep : Keep stepRegs s₀ u

/-- `CS` after a change of `combOut` that keeps the counters and the
accumulator, and registers that `CS` does not read. -/
theorem CS.frame {s₀ u v : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n A n' A' : Nat}
    (h : CS s₀ B C X Z w xb P G bits n A u) {rs : List Reg} (ho' : Outs B (rowOut w) u.mem v.mem)
    (k : Keep rs u v) (hrs : ∀ r ∈ rs, r ∈ stepRegs := by decide)
    (hI' : v.mem.readW (off B hI) 64 = BitVec.ofNat 64 n') (hacc : arr v.mem B w 6 = A') :
    CS s₀ B C X Z w xb P G bits n' A' v := by
  have ho := row_comb ho'
  have hfit := combOut_fit h.env
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hreg : ∀ r ∈ envRegs, r ∉ rs := fun r hr hr' => by
    have := hrs r hr'; simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [stepRegs] at this
  have hctx : Outside C (8 * ctxWords w) (2 ^ 64) u.mem v.mem := outs_ctx ho hfit h.ctx.sep
  refine ⟨h.env.keep k hreg, (k.gpr .r23 fun h' => by simpa [stepRegs] using hrs _ h').trans h.h23,
    (k.gpr .r28 fun h' => by simpa [stepRegs] using hrs _ h').trans h.h28,
    by rw [k.gpr .r12 fun h' => by simpa [stepRegs] using hrs _ h']; exact h.h12,
    by
      rw [k.gpr .r12 fun h' => by simpa [stepRegs] using hrs _ h', Pub.Outs.w32 ho (fun r hr => by
        simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
      exact h.hinv,
    h.ctx.congr (by rw [hdr_of_comb ho (by decide) (by decide)]; exact h.ctx.hC) k.rd k.wr,
    fun a ha => by
      rw [← h.ents a ha]
      exact Outside.val32 hctx (Or.inl (by have := row_fits (w := w) ha; omega))
        (by have := row_fits (w := w) ha; have := h.ctx.hn; omega),
    by
      rw [arr, Outs.val32 ho (fun r hr => by
        simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
      exact h.hp,
    hI', by rw [hdr_of_comb ho (by decide) (by decide)]; exact h.hRw,
    by rw [hdr_of_comb ho (by decide) (by decide)]; exact h.hX,
    fun n hn => by rw [k.rd, k.wr]; exact h.xrd n hn, h.xsep,
    fun n hn => by rw [byte_of_outs ho hfit (h.xsep n hn)]; exact h.xval n hn, hacc,
    by
      rw [arr, Outs.val32 ho' (fun r hr => by
        simp only [rowOut, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
      exact h.one,
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
      (32 ≤ r.1 ∧ r.1 + r.2 ≤ 56) ∨ (slot w 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 7) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  refine .inr ?_
  rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> (try rcases ho with rfl | rfl) <;> omega

theorem hdr_of_comb' {B : Addr} {w o x : Nat} {m m' : Mem}
    (h : Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] m m')
    (hx : x + 8 ≤ 256) : m'.readW (off B x) 64 = m.readW (off B x) 64 :=
  h.word (d := x) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by omega)

/-- One row: from `n + 1` rows left to `n`. -/
theorem step_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n : Nat} (hq : RowP P bits xb)
    (h : CS s₀ B C X Z w xb P G bits (n + 1) (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (n + 1))) u)
    (hn : n < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa step u fun v =>
      CS s₀ B C X Z w xb P G bits n (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) n)) v ∧
        v.gpr .r3 = BitVec.ofNat 64 n := by
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hP : 0 < P := by have := hq.one; omega
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h1 := hq.rows
  have hS : slot w 28 = 256 + 28 * (8 * (w + 2)) := rfl
  generalize hx : Spec.Rsa.os2ip xb = x at h ⊢
  unfold step
  simp only [seqs]
  -- The square.
  refine WP.seq (WP.mono (h.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.acc]; exact combM_lt hP _)) fun u₁ ⟨⟨lt1, eq1, o1⟩, k1⟩ => ?_)
  rw [h.acc] at eq1
  have a1 := Rsa.FixedBaseComb.mont_square_encoded cop lt1 rfl eq1
  have c1 := h.frame (to_row o1 (slot_row w 6 (.inr rfl))) k1 (by decide)
    (by rw [hdr_of_comb' o1 (by decide)]; exact h.hIw) a1
  -- The digit.
  have xc : XCtx u₁ B X Z xb n (Spec.Rsa.FixedBaseComb.rows bits) := ⟨c1.env.hs, by omega, c1.h23, c1.h28,
    c1.hIw, c1.hRw, c1.hX, c1.xrd, c1.xval, by omega, hq.len⟩
  refine WP.seq (WP.mono (digit_ok xc) fun u₂ ⟨m2, k2⟩ => ?_)
  rw [hx, combDigit_eq, show hD = 40 from rfl] at m2
  have hd := Rsa.FixedBaseComb.digit_lt bits x n
  have o2 : Outs B (rowOut w) u₁.mem u₂.mem := by
    rw [m2]; exact to_row (Outs.of_outside (rs := [(40, 8)]) (writeW_outside _ B (d := 40) _ (by omega)) (by simp))
      (by simp)
  have c2 := c1.frame (A' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1))) o2 k2 (by decide)
    (by rw [m2]; exact (Outside.word (d := hI) (writeW_outside _ B (d := 40) _ (by omega)) (Or.inl (by decide))
      (by unfold hI; omega)).trans c1.hIw) (by
    rw [arr, m2, Outside.val32 (writeW_outside _ B (d := 40) _ (by omega)) (Or.inr (by simp only [slot]; omega))
      (by simp only [slot] at hZ ⊢; omega)]; exact c1.acc)
  -- The entry.
  refine WP.seq (WP.mono (select_ok c2.env c2.h23 c2.ctx (by rw [m2]; exact Mem.readW_writeW_self64 _ _ _) hd)
    fun u₃ ⟨⟨a3, o3⟩, k3⟩ => ?_)
  rw [c2.ents _ hd] at a3
  have o3' : Outs B (rowOut w) u₂.mem u₃.mem := to_row o3 (fun r hr => by
    simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨by decide, by decide⟩
    · exact .inr ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩)
  have c3 := c2.frame (A' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1))) o3' k3 (by decide) (by
      rw [hdr_of_outs o3 (by decide)]; exact c2.hIw) (by
    rw [arr, Outs.val32 o3 (fun r hr => by
      simp only [selOut, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, hdrBytes, hJ] <;> omega) (by simp only [slot] at hZ ⊢; omega)]
    exact c2.acc)
  -- The product.
  refine WP.seq (WP.mono (c3.mont (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [a3]; exact combM_lt hP _)) fun u₄ ⟨⟨lt4, eq4, o4⟩, k4⟩ => ?_)
  rw [c3.acc, a3] at eq4
  have a4 := Rsa.FixedBaseComb.mont_product_encoded cop lt4 rfl rfl eq4
  rw [← Rsa.FixedBaseComb.high_step bits x n hn] at a4
  have c4 := c3.frame (to_row o4 (slot_row w 6 (.inr rfl))) k4 (by decide)
    (by rw [hdr_of_comb' o4 (by decide)]; exact c3.hIw) a4
  -- `hI := n`.
  have l32 : InRegions (u₄.rd ++ u₄.wr) (u₄.gpr .r23 + BitVec.ofNat 64 32) 8 := by
    rw [c4.h23]; exact c4.env.hs.ld (d := 32) (n := 8) (by simp only [slot] at hZ; omega)
  have s32 : InRegions u₄.wr (u₄.gpr .r23 + BitVec.ofNat 64 32) 8 := by
    rw [c4.h23]; exact c4.env.hs.st (d := 32) (n := 8) (by simp only [slot] at hZ; omega)
  have v32 : u₄.mem.readW (u₄.gpr .r23 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (n + 1) := by
    rw [c4.h23]; exact c4.hIw
  refine WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 n ∧
      v.mem = u₄.mem.writeW (off B 32) (BitVec.ofNat 64 n)) (by
    unfold ldh sth
    prun [hI, l32, s32, v32, ofNat_sub_one (show 1 ≤ n + 1 by omega) (show n + 1 < 2 ^ 64 by omega), Nat.add_sub_cancel]
    rw [c4.h23]) (by decide)) fun v ⟨⟨a5, m5⟩, k5⟩ => ⟨?_, a5⟩
  refine c4.frame (by
      rw [m5]; exact to_row (Outs.of_outside (rs := [(32, 8)]) (writeW_outside _ B (d := 32) _ (by omega))
        (by simp)) (by simp)) k5 (by decide)
    (by rw [m5]; exact Mem.readW_writeW_self64 _ _ _) (by
    rw [arr, m5, Outside.val32 (writeW_outside _ B (d := 32) _ (by omega)) (Or.inr (by simp only [slot]; omega))
      (by simp only [slot] at hZ ⊢; omega)]; exact c4.acc)

/-! ## The comb -/

/-- What the comb needs: the working space with p in array 0, the context
(its address in the header) and its entries, x's octets (their address in the
header) and the header's row count. -/
structure CombIn (s : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits : Nat) : Prop where
  env : Env s B Z w
  h23 : s.gpr .r23 = B
  h28 : s.gpr .r28 = BitVec.ofNat 64 xb.length
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
def combRegs : List Reg := .r12 :: stepRegs

theorem row1_fits (w : Nat) : rowOff w 1 + 8 * w ≤ 8 * ctxWords w := by unfold rowOff ctxWords; omega

/-- The rows, from `n` left, by `wp_countdown` on `r3`. -/
theorem rows_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat} (hq : RowP P bits xb)
    (h : CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) u)
    (h3 : u.gpr .r3 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) (hpos : 0 < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa (.loop step (.nonzero .d .r3)) u
      (CS s₀ B C X Z w xb P G bits 0 (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0))) := by
  have h1 := hq.rows
  refine WP.mono (wp_countdown (body := step) (cnt := .r3) (N := Spec.Rsa.FixedBaseComb.rows bits) (by omega) hpos
    (fun i v => CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits - i)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits - i))) v)
    (fun i hi v hv hc => ?_) (by simpa using h) h3) fun v hv => by simpa using hv
  have e : Spec.Rsa.FixedBaseComb.rows bits - i = Spec.Rsa.FixedBaseComb.rows bits - (i + 1) + 1 := by omega
  rw [e] at hv hc
  refine WP.mono (step_ok hq hv (by omega)) fun v' ⟨hv', a3⟩ => ⟨hv', ?_⟩
  rw [a3, hc, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]

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
  have hS : slot w 28 = 256 + 28 * (8 * (w + 2)) := rfl
  have hfit := combOut_fit h.env
  unfold comb
  simp only [seqs]
  -- `r3 := 1`.
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 1 ∧ u.mem = s.mem) (by prun)
    (by decide)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have e1 := h.env.keep k1 (by decide)
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (loadRow_ok (a := 1) (j := 1) (Zc := 8 * ctxWords w) e1 ((k1.gpr .r23 (by decide)).trans h.h23)
    (by rw [m1]; exact h.ctx.hC) a3 (by decide) (by decide) (row1_fits w) h.ctx.hn
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
  have e5 := e4.keep k5 (by decide)
  have o15 : Outs B (combOut w) s.mem s₅.mem := by
    have h1 : Outs B (combOut w) s.mem s₂.mem := to_comb (Outs.of_outside (rs := [(slot w 1, 8 * w)]) o2 (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr; subst hr
          exact .inr ⟨Nat.le_refl _, by simp only [slot]; omega⟩)
    have h2 : Outs B (combOut w) s₂.mem s₄.mem := to_comb (Outs.of_outside (rs := [(slot w 7, 8 * w)]) o4 (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr; subst hr
          exact .inr ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩)
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
  have g23 : s₅.gpr .r23 = B := (k15.gpr .r23 (by decide)).trans h.h23
  -- `hI := rows`.
  have l24 : InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .r23 + BitVec.ofNat 64 24) 8 := by
    rw [g23]; exact e5.hs.ld (d := 24) (n := 8) (by simp only [slot] at hZ; omega)
  have v24 : s₅.mem.readW (s₅.gpr .r23 + BitVec.ofNat 64 24) 64 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) := by
    rw [g23, hdr_of_comb o15 (by decide) (by decide)]; exact h.hRw
  have s32 : InRegions s₅.wr (s₅.gpr .r23 + BitVec.ofNat 64 32) 8 := by
    rw [g23]; exact e5.hs.st (d := 32) (n := 8) (by simp only [slot] at hZ; omega)
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      v.mem = s₅.mem.writeW (off B 32) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits))) (by
    unfold ldh sth; prun [hRows, hI, l24, v24, s32]; rw [g23]) (by decide)) fun s₆ ⟨⟨a6, m6⟩, k6⟩ => ?_)
  have o6 : Outs B (rowOut w) s₅.mem s₆.mem := by
    rw [m6]; exact to_row (Outs.of_outside (rs := [(32, 8)]) (writeW_outside _ B (d := 32) _ (by omega))
      (by simp)) (by simp)
  have k16 := k15.trans k6
  have hpos := Rsa.FixedBaseComb.rows_pos h.pos
  have hw6 : ∀ x, (x + 8 ≤ 32 ∨ 56 ≤ x) → x + 8 ≤ 256 → s₆.mem.readW (off B x) 64 = s.mem.readW (off B x) 64 :=
    fun x hx hx' => by rw [hdr_of_comb (row_comb o6) hx hx', hdr_of_comb o15 hx hx']
  have c6 : CS s₆ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) s₆ := by
    have hctx : Outside C (8 * ctxWords w) (2 ^ 64) s.mem s₆.mem := outs_ctx (o15.trans (row_comb o6)) hfit h.ctx.sep
    have hO : ∀ j, j = 0 ∨ j = 6 ∨ j = 7 → arr s₆.mem B w j = arr s₅.mem B w j := fun j hj => by
      rw [arr, arr, m6, Outside.val32 (writeW_outside _ B (d := 32) _ (by omega))
        (Or.inr (by rcases hj with rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega))
        (by rcases hj with rfl | rfl | rfl <;> simp only [slot] at hZ ⊢ <;> omega)]
    refine ⟨e5.keep k6 (by decide), (k6.gpr .r23 (by decide)).trans g23, (k16.gpr .r28 (by decide)).trans h.h28,
      by rw [k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), g12]; exact r12lt,
      by
        rw [k6.gpr .r12 (by decide), k5.gpr .r12 (by decide), g12, m6,
          Outside.w32 (writeW_outside _ B (d := 32) _ (by omega)) (Or.inr (by simp only [slot, hdrBytes]; omega))
            (by simp only [slot] at hZ ⊢; omega),
          Pub.Outs.w32 o5 (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega) (by simp only [slot] at hZ ⊢; omega), w4]
        exact r12inv,
      h.ctx.congr (by rw [show hCtx = 0 from rfl, hw6 0 (by decide) (by decide)]; exact h.ctx.hC) k16.rd k16.wr,
      fun a ha => by
        rw [← h.ents a ha]
        exact Outside.val32 hctx (Or.inl (by have := row_fits (w := w) ha; omega))
          (by have := row_fits (w := w) ha; have := h.ctx.hn; omega),
      by rw [hO 0 (.inl rfl)]; exact p5,
      by rw [m6]; exact Mem.readW_writeW_self64 _ _ _,
      by rw [show hRows = 24 from rfl, hw6 24 (by decide) (by decide)]; exact h.hRw,
      by rw [hw6 64 (by decide) (by decide)]; exact h.hX,
      fun n hn => by rw [k16.rd, k16.wr]; exact h.xrd n hn, h.xsep,
      fun n hn => by rw [byte_of_outs (o15.trans (row_comb o6)) hfit (h.xsep n hn)]; exact h.xval n hn,
      by rw [hO 6 (.inr (.inl rfl))]; exact a5,
      by rw [hO 7 (.inr (.inr rfl))]; exact one5,
      Outs.refl _ _ _, Keep.refl _ _⟩
  -- The rows.
  refine WP.seq (WP.mono (rows_ok hq c6 a6 hpos) fun v hv => ?_)
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
  · exact ((o15.trans (row_comb o6)).trans hv.out).trans (row_comb (to_row o7 (slot_row w 4 (.inl rfl))))
  · exact (k7.gpr .r10 (by decide)).trans hv.env.h10
  · exact ((k16.trans hv.keep).trans k7).mono (by decide)

end VG.Proof.Ffdh.PPC64LE.Cached
