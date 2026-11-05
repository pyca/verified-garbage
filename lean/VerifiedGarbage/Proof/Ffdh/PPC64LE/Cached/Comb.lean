module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Digit
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Cut
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

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

end VG.Proof.Ffdh.PPC64LE.Cached
