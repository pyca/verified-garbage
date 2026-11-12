module

import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: the subtraction

`mulSub` replaces the `w` words `x` at `x11` by the `w + 1` words
`t = x 2^64 - q m` modulo `2^(64 (w + 1))`, for `m` the `w` words at `x9`:
`t + q m = x 2^64 + 2^(64 (w + 1)) b` (`mulSub_ok`). It sums the complement
`~t = ~(x 2^64) + q m` (`msWord_arith`, `msTop_arith`).
`addBack` adds `m` to the `w + 1` words `t` if `t ≥ 2^(64 (w + 1)) / 2`
(its sign, in two's complement): `t' + 2^(64 (w + 1)) c = t + m` for the
carry `c` (`r2dAddBack_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `adcs`, as numbers. -/
theorem adcs_val (a b : BitVec 64) (c : Bool) :
    (a + b + BitVec.ofNat 64 c.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : c.toNat < 2 ^ 64)]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The complement of a word: `x ^ allOnes` is `2^64 - 1 - x`. -/
theorem xor_ones_toNat (x : BitVec 64) : (x ^^^ BitVec.allOnes 64).toNat = 2 ^ 64 - 1 - x.toNat := by
  rw [BitVec.xor_allOnes, BitVec.toNat_not]

/-- All ones, as `mulSubHead` makes it. -/
theorem r2d_ones : (BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide

/-- A word of `mulSub`: the carries in (`c` and `C`), the word `t` and the
product `q m` are the previous word `p` of `x` and the carries out. -/
theorem msWord_arith (q m c p : BitVec 64) (C : Bool) :
    c.toNat + C.toNat + ((q * m + c + BitVec.ofNat 64 C.toNat + ~~~p + BitVec.ofNat 64 (false : Bool).toNat) ^^^
        BitVec.allOnes 64).toNat + q.toNat * m.toNat =
      p.toNat + 2 ^ 64 * ((BitVec.ofNat 64 (q.toNat * m.toNat / 2 ^ 64) + 0 +
        BitVec.ofNat 64 (decide (2 ^ 64 ≤ (q * m).toNat + c.toNat + C.toNat)).toNat).toNat +
        (decide (2 ^ 64 ≤ (q * m + c + BitVec.ofNat 64 C.toNat).toNat + (~~~p).toNat +
          (false : Bool).toNat)).toNat) := by
  have e1 := adcs_val (q * m) c C
  have e2 := adcs_val (q * m + c + BitVec.ofNat 64 C.toNat) (~~~p) false
  rw [xor_ones_toNat]
  generalize decide (2 ^ 64 ≤ (q * m).toNat + c.toNat + C.toNat) = k1 at e1 ⊢
  generalize (q * m + c + BitVec.ofNat 64 C.toNat) = s1 at e1 e2 ⊢
  generalize decide (2 ^ 64 ≤ s1.toNat + (~~~p).toNat + (false : Bool).toNat) = k2 at e2 ⊢
  generalize hs2 : s1 + ~~~p + BitVec.ofNat 64 (false : Bool).toNat = s2 at e2 ⊢
  have hqm : (q * m).toNat = q.toNat * m.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have hd := Nat.div_add_mod (q.toNat * m.toNat) (2 ^ 64)
  have hq := q.isLt; have hm := m.isLt
  have hhi : q.toNat * m.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := Nat.le_trans (Nat.div_le_div_right (c := 2 ^ 64)
    (Nat.mul_le_mul (show q.toNat ≤ 2 ^ 64 - 1 by omega_arith) (show m.toNat ≤ 2 ^ 64 - 1 by omega_arith)))
    (by decide)
  have hk1 := Bool.toNat_le k1
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  simp only [Nat.mod_eq_of_lt (show q.toNat * m.toNat / 2 ^ 64 < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show k1.toNat < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show q.toNat * m.toNat / 2 ^ 64 + k1.toNat < 2 ^ 64 by omega_arith)]
  rw [BitVec.toNat_not] at e2
  have := s2.isLt; have := p.isLt
  simp only [Bool.toNat_false, Nat.add_zero] at e2
  rw [hqm] at e1
  generalize q.toNat * m.toNat = P at hd e1 hhi ⊢
  generalize P / 2 ^ 64 = hi at hd hhi ⊢
  generalize P % 2 ^ 64 = lo at hd e1 ⊢
  omega_arith

/-- The top word of `mulSub`: `~(~p + c + C)` and the carries in are `p` and
a carry out. -/
theorem msTop_arith (c p : BitVec 64) (C : Bool) : ∃ k : Bool,
    c.toNat + C.toNat + ((~~~p + c + BitVec.ofNat 64 C.toNat) ^^^ BitVec.allOnes 64).toNat =
      p.toNat + 2 ^ 64 * k.toNat := by
  have e := adcs_val (~~~p) c C
  rw [xor_ones_toNat]
  generalize decide (2 ^ 64 ≤ (~~~p).toNat + c.toNat + C.toNat) = k at e
  rw [BitVec.toNat_not] at e
  have := p.isLt; have := c.isLt; have := Bool.toNat_le C
  have hr := (~~~p + c + BitVec.ofNat 64 C.toNat).isLt
  generalize (~~~p + c + BitVec.ofNat 64 C.toNat).toNat = r at e hr ⊢
  refine ⟨k, ?_⟩
  cases k <;> simp only [Bool.toNat_false, Bool.toNat_true] at e ⊢ <;> omega_arith

/-- A word of `mulSub`'s sum, as numbers. -/
theorem ms_arith {A q Mj X W cc Y p tj mj c : Nat} (hval : A + q * Mj = X + W * cc) (hp : Y = X + W * p)
    (hw : cc + tj + q * mj = p + 2 ^ 64 * c) : A + W * tj + q * (Mj + W * mj) = Y + W * 2 ^ 64 * c := by
  have e := congrArg (W * ·) hw
  simp only [Nat.mul_add] at e
  rw [Nat.mul_add, Nat.mul_left_comm q W mj, hp, Nat.mul_assoc W]
  omega_arith

/-- The word below `x`'s word `j` in `x 2^64 + u`: `u` below the first. -/
def msPrev (m : Mem) (B : Addr) (eX : Nat) (u : BitVec 64) (j : Nat) : BitVec 64 :=
  if j = 0 then u else word m B (eX + 8 * (j - 1))

theorem msPrev_zero (m : Mem) (B : Addr) (eX : Nat) (u : BitVec 64) : msPrev m B eX u 0 = u := by simp [msPrev]

theorem msPrev_succ (m : Mem) (B : Addr) (eX : Nat) (u : BitVec 64) (j : Nat) :
    msPrev m B eX u (j + 1) = word m B (eX + 8 * j) := by
  simp [msPrev]

/-- The low `j` words of `x 2^64 + u`. -/
def msLow (m : Mem) (B : Addr) (eX u j : Nat) : Nat := 2 ^ 64 * wv m B eX (j - 1) + if j = 0 then 0 else u

/-- `msLow` over one more word. -/
theorem msLow_succ (m : Mem) (B : Addr) (eX : Nat) (u : BitVec 64) (j : Nat) :
    msLow m B eX u.toNat (j + 1) = msLow m B eX u.toNat j + 2 ^ (64 * j) * (msPrev m B eX u j).toNat := by
  rcases j with _ | j
  · simp [msLow, msPrev, wv]
  · rw [msPrev_succ, msLow, msLow, Nat.add_sub_cancel, Nat.add_sub_cancel, wv, pow64_succ, Nat.mul_add,
      Nat.mul_comm (2 ^ (64 * j)) (2 ^ 64), Nat.mul_assoc]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    omega_arith

/-- After `j` words of `mulSub`'s loop, from the memory `m₀` and the state
`s₀` after its head, for `q̂ = q` and the word `u` below `x`:
`t + q m = x 2^64 + u + 2^(64 j) (c + C)` over `j` words, and the
complement of the word below `j` in `x13`. -/
structure MSInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eX eM q : Nat) (u : BitVec 64) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4, .x13, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eM + 8 * j)
  x13 : t.gpr .x13 = ~~~msPrev m₀ B eX u j
  out : Outside B eX (8 * j) m₀ t.mem
  val : wv t.mem B eX j + q * wv m₀ B eM j = msLow m₀ B eX u.toNat j +
    2 ^ (64 * j) * ((t.gpr .x2).toNat + t.c.toNat)

theorem msStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eX eM q : Nat}
    (h1 : s₀.gpr .x1 = BitVec.ofNat 64 q) (hq : q < 2 ^ 64) (h7 : s₀.gpr .x7 = 0)
    (h15 : s₀.gpr .x15 = BitVec.allOnes 64) (hX : eX + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z)
    (sM : eX + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eX) {j : Nat} (hj : j < w)
    {u : BitVec 64} {t : State} (hI : MSInv m₀ s₀ B Z eX eM q u j t) :
    WP isa (.block (mulSubWord ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      MSInv m₀ s₀ B Z eX eM q u (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t1 : t.gpr .x1 = BitVec.ofNat 64 q := (hI.keep.gpr .x1 (by decide)).trans h1
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t15 : t.gpr .x15 = BitVec.allOnes 64 := (hI.keep.gpr .x15 (by decide)).trans h15
  have hx : word t.mem B (eX + 8 * j) = word m₀ B (eX + 8 * j) :=
    hI.out.word (d := eX + 8 * j) (Or.inr (Nat.le_refl _)) (by omega_arith)
  have hy : word t.mem B (eM + 8 * j) = word m₀ B (eM + 8 * j) :=
    hI.out.word (d := eM + 8 * j) (by omega_arith) (by omega_arith)
  generalize hQ : (BitVec.ofNat 64 q : BitVec 64) = Q at t1
  generalize hP : msPrev m₀ B eX u j = P
  have hx13 : t.gpr .x13 = ~~~P := hP ▸ hI.x13
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x2, .x3, .x4, .x13, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) ((Q * word t.mem B (eM + 8 * j) + t.gpr .x2 +
        BitVec.ofNat 64 t.c.toNat + ~~~P + BitVec.ofNat 64 (false : Bool).toNat) ^^^ BitVec.allOnes 64) ∧
      t₁.gpr .x2 = BitVec.ofNat 64 (Q.toNat * (word t.mem B (eM + 8 * j)).toNat / 2 ^ 64) + 0 +
        BitVec.ofNat 64 (decide (2 ^ 64 ≤ (Q * word t.mem B (eM + 8 * j)).toNat + (t.gpr .x2).toNat +
          t.c.toNat)).toNat ∧
      t₁.c = decide (2 ^ 64 ≤ (Q * word t.mem B (eM + 8 * j) + t.gpr .x2 + BitVec.ofNat 64 t.c.toNat).toNat +
        (~~~P).toNat + (false : Bool).toNat) ∧
      t₁.gpr .x13 = word t.mem B (eX + 8 * j) ^^^ BitVec.allOnes 64 ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eM + 8 * j + 8))
    (by brun [mulSubWord, hI.x16, hI.x17, t1, t7, t15, hx13, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h2, hc, h13, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_⟩
  · rw [k'.gpr .x13 (by decide), h13, hx, msPrev_succ, BitVec.xor_allOnes]
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)).trans (hI.out x (by omega_arith))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hc', hc, k'.gpr .x2 (by decide), h2,
      show wv m₀ B eM (j + 1) = wv m₀ B eM j + 2 ^ (64 * j) * (word m₀ B (eM + 8 * j)).toNat from rfl,
      pow64_succ]
    have hw := msWord_arith Q (word t.mem B (eM + 8 * j)) (t.gpr .x2) P t.c
    have hQn : Q.toNat = q := by rw [← hQ, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
    have hv := hI.val
    rw [hy] at hw ⊢
    rw [← hQn] at hv ⊢
    have hp := msLow_succ m₀ B eX u j
    rw [hP] at hp
    exact ms_arith hv hp hw


/-- `mulSub`'s loop and top word, from its head: `t = x 2^64 + u - q m`
modulo `2^(64 (w + 1))` over the `w + 1` words of `x` (at `x16`), for `m`
the `w` words at `x17`, `q` in `x1` and `~u` in `x13`. -/
theorem mulSubLoop_ok {s : State} {B : Addr} {Z w eX eM q : Nat} {u : BitVec 64} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eM) (h14 : s.gpr .x14 = BitVec.ofNat 64 w)
    (h2 : s.gpr .x2 = 0) (h15 : s.gpr .x15 = BitVec.allOnes 64) (h13 : s.gpr .x13 = ~~~u) (hc : s.c = false)
    (h7 : s.gpr .x7 = 0) (h1 : s.gpr .x1 = BitVec.ofNat 64 q) (hq : q < 2 ^ 64) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eX) :
    WP isa (.seq (countLoop .x14 mulSubWord) (.block mulSubTop)) s fun t => ∃ b : Bool,
      wv t.mem B eX (w + 1) + q * wv s.mem B eM w =
        2 ^ 64 * wv s.mem B eX w + u.toNat + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B eX (8 * (w + 1)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  have h0 : MSInv s.mem s B Z eX eM q u 0 s := by
    refine ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13, msPrev_zero],
      Outside.refl _ _ _ _, ?_⟩
    rw [h2, hc]; simp [msLow, wv]
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (MSInv s.mem s B Z eX eM q u)
    (fun j hj t hI _ => msStep_ok h1 hq h7 h15 hX hM sM hj hI) h0 h14) fun t hI => ?_)
  have t15 : t.gpr .x15 = BitVec.allOnes 64 := (hI.keep.gpr .x15 (by decide)).trans h15
  generalize hP : msPrev s.mem B eX u w = P
  have hx13 : t.gpr .x13 = ~~~P := hP ▸ hI.x13
  refine WP.mono (WP.keep [.x4] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (eX + 8 * w)) ((~~~P + t.gpr .x2 + BitVec.ofNat 64 t.c.toNat) ^^^ BitVec.allOnes 64))
    (by brun [mulSubTop, hI.x16, hx13, t15, hI.scr.st (show eX + 8 * w + 8 ≤ Z by omega_arith)]) (by decide) (by decide)
    (by decide +kernel)) fun t' ⟨hm', k'⟩ => ?_
  obtain ⟨k, hk⟩ := msTop_arith (t.gpr .x2) P t.c
  refine ⟨k, ?_, ?_, (hI.keep.trans k').mono (by decide)⟩
  · rw [hm', wv_writeW_top _ _ _ _ _ (by omega_arith), pow64_succ]
    have hp := msLow_succ s.mem B eX u w
    rw [hP] at hp
    have e := ms_arith (mj := 0) hI.val hp (by rw [Nat.mul_zero, Nat.add_zero]; exact hk)
    rw [Nat.mul_zero, Nat.add_zero] at e
    have hl : msLow s.mem B eX u.toNat (w + 1) = 2 ^ 64 * wv s.mem B eX w + u.toNat := by
      simp only [msLow, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hl] at e
    exact e
  · rw [hm']
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)).trans (hI.out x (by omega_arith))

/-- `mulSub`: `t = x 2^64 - q m` modulo `2^(64 (w + 1))` over the `w + 1`
words of `x` (at `x11`), for `m` the `w` words at `x9` and `q` in `x1`:
`t + q m = x 2^64 + 2^(64 (w + 1)) b`. -/
theorem mulSub_ok {s : State} {B : Addr} {Z w eX eM q : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eX) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (h1 : s.gpr .x1 = BitVec.ofNat 64 q) (hq : q < 2 ^ 64) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eX) :
    WP isa mulSub s fun t => ∃ b : Bool,
      wv t.mem B eX (w + 1) + q * wv s.mem B eM w = 2 ^ 64 * wv s.mem B eX w + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B eX (8 * (w + 1)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x13, .x14, .x15, .x16, .x17] s t := by
  unfold mulSub
  refine WP.seq (WP.mono (WP.keep [.x2, .x3, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
    t.gpr .x16 = off B eX ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧
    t.gpr .x15 = BitVec.allOnes 64 ∧ t.gpr .x13 = ~~~(0 : BitVec 64) ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [mulSubHead, h11, h9, h12, h7, r2d_ones]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, h2, h15, h13, hc₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (mulSubLoop_ok (hs.congr k₁.wr) h16 h17 h14 h2 h15 h13 hc₁ ((k₁.gpr .x7 (by decide)).trans h7)
    ((k₁.gpr .x1 (by decide)).trans h1) hq hw hw' hX hM sM) fun t ⟨b, hv, o, k⟩ => ⟨b, ?_, ?_, (k₁.trans k).mono (by decide)⟩
  · rw [hm₁] at hv; simpa using hv
  · rw [hm₁] at o; exact o

/-- `mulSubU`: `t = x 2^64 + u - q m` modulo `2^(64 (w + 1))`, for `u` in `x10`. -/
theorem mulSubU_ok {s : State} {B : Addr} {Z w eX eM q : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eX) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (h1 : s.gpr .x1 = BitVec.ofNat 64 q) (hq : q < 2 ^ 64) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eX) :
    WP isa mulSubU s fun t => ∃ b : Bool,
      wv t.mem B eX (w + 1) + q * wv s.mem B eM w =
        2 ^ 64 * wv s.mem B eX w + (s.gpr .x10).toNat + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B eX (8 * (w + 1)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x13, .x14, .x15, .x16, .x17] s t := by
  unfold mulSubU
  refine WP.seq (WP.mono (WP.keep [.x2, .x3, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
    t.gpr .x16 = off B eX ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧
    t.gpr .x15 = BitVec.allOnes 64 ∧ t.gpr .x13 = ~~~(s.gpr .x10) ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [mulSubHeadU, h11, h9, h12, h7, r2d_ones, BitVec.xor_allOnes]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, h2, h15, h13, hc₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (mulSubLoop_ok (hs.congr k₁.wr) h16 h17 h14 h2 h15 h13 hc₁ ((k₁.gpr .x7 (by decide)).trans h7)
    ((k₁.gpr .x1 (by decide)).trans h1) hq hw hw' hX hM sM) fun t ⟨b, hv, o, k⟩ => ⟨b, ?_, ?_, (k₁.trans k).mono (by decide)⟩
  · rw [hm₁] at hv; exact hv
  · rw [hm₁] at o; exact o

/-! ## `R - m` -/

/-- After `j` words of `neg`'s loop: `x_j + m_j = 2^(64 j) b` for the borrow `b`. -/
structure R2dNegInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eX eM : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eM + 8 * j)
  out : Outside B eX (8 * j) m₀ t.mem
  val : wv t.mem B eX j + wv m₀ B eM j = 2 ^ (64 * j) * (!t.c).toNat

theorem r2dNegStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eX eM : Nat} (h7 : s₀.gpr .x7 = 0)
    (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * w ≤ eM ∨ eM + 8 * w ≤ eX) {j : Nat} (hj : j < w)
    {t : State} (hI : R2dNegInv m₀ s₀ B Z eX eM j t) :
    WP isa (.block ([ld .x4 .x17, .sbcs .x .x3 .x7 .x4, st .x3 .x16, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      R2dNegInv m₀ s₀ B Z eX eM (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) (0 + ~~~word t.mem B (eM + 8 * j) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (0 : BitVec 64).toNat + (~~~word t.mem B (eM + 8 * j)).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eM + 8 * j + 8))
    (by brun [hI.x16, hI.x17, t7, hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hy : word t.mem B (eM + 8 * j) = word m₀ B (eM + 8 * j) :=
    hI.out.word (d := eM + 8 * j) (by omega_arith) (by omega_arith)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)).trans (hI.out x (by omega_arith))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hc', hc]
    have hs := sbcs_toNat 0 (word t.mem B (eM + 8 * j)) t.c
    rw [hy] at hs ⊢
    have hval := hI.val
    rw [wv, pow64_succ]
    simp only [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, Nat.zero_add] at hs ⊢
    generalize (0 + ~~~word m₀ B (eM + 8 * j) + BitVec.ofNat 64 t.c.toNat).toNat = r at hs ⊢
    generalize 2 ^ (64 * j) = P at hval ⊢
    have e : wv t.mem B eX j + P * r + (wv m₀ B eM j + P * (word m₀ B (eM + 8 * j)).toNat) =
        (wv t.mem B eX j + wv m₀ B eM j) + P * (r + (word m₀ B (eM + 8 * j)).toNat) := by
      rw [Nat.mul_add]; omega_arith
    rw [e, hval, ← Nat.mul_add, Nat.mul_assoc]
    exact congrArg (P * ·) (by omega_arith)

/-- `neg`: `x := R - m` over `w` words (`x` at `x11`, `m` at `x9`):
`x + m = 2^(64 w) b` for the borrow `b`. -/
theorem r2dNeg_ok {s : State} {B : Addr} {Z w eX eM : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eX) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * w ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eX + 8 * w ≤ eM ∨ eM + 8 * w ≤ eX) :
    WP isa neg s fun t => ∃ b : Bool,
      wv t.mem B eX w + wv s.mem B eM w = 2 ^ (64 * w) * b.toNat ∧
      Outside B eX (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold neg
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x16, .x17] (Q := fun t =>
    t.gpr .x16 = off B eX ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [h11, h9, h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : R2dNegInv s.mem s₁ B Z eX eM 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (R2dNegInv s.mem s₁ B Z eX eM)
    (fun j hj t hI _ => r2dNegStep_ok ((k₁.gpr .x7 (by decide)).trans h7) hX hM sM hj hI) h0 h14) fun t hI => ?_
  exact ⟨!t.c, hI.val, hI.out, (k₁.trans hI.keep).mono (by decide)⟩

/-! ## Adding `m` back -/

/-- The mask of the top bit of `v`: `0 - (v >>> 63)`. -/
theorem sign_mask (v : BitVec 64) : 0 - v >>> 63 = mask (decide (2 ^ 63 ≤ v.toNat)) := by
  have hv := v.isLt
  have e : v >>> 63 = (BitVec.ofBool (decide (2 ^ 63 ≤ v.toNat))).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    by_cases h : 2 ^ 63 ≤ v.toNat <;> simp only [h, decide_true, decide_false] <;>
      (show _ = BitVec.toNat (BitVec.setWidth 64 (BitVec.ofBool _)); simp) <;> omega_arith
  rw [e]; rfl

/-- `(w <<< 3)` is `8 w`. -/
theorem r2d_ofNat_shl3 {w : Nat} (hw : w < 2 ^ 61) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega_arith : w < 2 ^ 64)]
  omega_arith

/-- The sign of a number of `w + 1` words is its top word's top bit. -/
theorem sign_top (m : Mem) (B : Addr) (eA w : Nat) :
    decide (2 ^ 63 ≤ (word m B (eA + 8 * w)).toNat) = decide (2 ^ (64 * (w + 1)) / 2 ≤ wv m B eA (w + 1)) := by
  have hP : 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
  have hl := wv_lt m B eA w
  have hd : wv m B eA (w + 1) / 2 ^ (64 * w) = (word m B (eA + 8 * w)).toNat := by
    rw [wv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl, Nat.zero_add]
  apply decide_eq_decide.mpr
  rw [hP, ← hd, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm (2 ^ 63)]

/-- A word of `addBack`'s sum. -/
theorem addB_arith {A M W P r a mj co ci : Nat} (g : Bool) (h : A + P * ci = M + (if g then W else 0))
    (hs : r + 2 ^ 64 * co = a + (if g then mj else 0) + ci) :
    A + P * r + P * 2 ^ 64 * co = M + P * a + (if g then W + P * mj else 0) := by
  have e : A + P * r + P * 2 ^ 64 * co = A + P * (r + 2 ^ 64 * co) := by
    rw [Nat.mul_add, Nat.mul_assoc]; omega_arith
  rw [e, hs]
  cases g
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h ⊢
    rw [Nat.mul_add]; omega_arith
  · simp only [↓reduceIte] at h ⊢
    rw [Nat.mul_add, Nat.mul_add]; omega_arith

/-- The top word of `addBack`'s sum. -/
theorem addB_tail {Wt Ws P r co top c G : Nat} (h : Wt + P * c = Ws + G) (hs : r + 2 ^ 64 * co = top + 0 + c) :
    Wt + P * r + P * 2 ^ 64 * co = Ws + P * top + G := by
  rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hs, Nat.add_zero, Nat.mul_add]
  omega_arith

/-- After `j` words of `addBack`'s loop, from the memory `m₀` and the state
`s₀` after its head, adding `m` if `g`. -/
structure AddBInv (m₀ : Mem) (s₀ : State) (B : Addr) (Z eA eM : Nat) (g : Bool) (j : Nat) (t : State) :
    Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eM + 8 * j)
  out : Outside B eA (8 * j) m₀ t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * t.c.toNat = wv m₀ B eA j + if g then wv m₀ B eM j else 0

theorem addBStep_ok {m₀ : Mem} {s₀ : State} {B : Addr} {Z w eA eM : Nat} {g : Bool}
    (h15 : s₀.gpr .x15 = mask g) (hA : eA + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z)
    (sM : eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) {j : Nat} (hj : j < w)
    {t : State} (hI : AddBInv m₀ s₀ B Z eA eM g j t) :
    WP isa (.block ([ld .x4 .x17, .logic .and .x .x4 .x4 .x15, ld .x3 .x16, .adcs .x .x3 .x3 .x4, st .x3 .x16,
        next .x16, next .x17] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      AddBInv m₀ s₀ B Z eA eM g (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask g := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (word t.mem B (eA + 8 * j) +
        (word t.mem B (eM + 8 * j) &&& mask g) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * j)).toNat + (word t.mem B (eM + 8 * j) &&& mask g).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eM + 8 * j + 8))
    (by brun [hI.x16, hI.x17, t15, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eM + 8 * j) = word m₀ B (eM + 8 * j) :=
    hI.out.word (d := eM + 8 * j) (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eA + 8 * j) = word m₀ B (eA + 8 * j) :=
    hI.out.word (d := eA + 8 * j) (Or.inr (Nat.le_refl _)) (by omega_arith)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)).trans (hI.out x (by omega_arith))
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hc', hc]
    have hs := adcs_val (word t.mem B (eA + 8 * j)) (word t.mem B (eM + 8 * j) &&& mask g) t.c
    rw [and_mask_toNat, hx, hy] at hs
    rw [and_mask_toNat, hx, hy, pow64_succ, wv, wv]
    exact addB_arith g hI.val hs

/-- `addBack`: `m` (the `w` words at `x9`) added to the `w + 1` words `t` of
`x` (at `x11`) if `t ≥ 2^(64 (w + 1)) / 2`, with the carry `c`
out of the top word. -/
theorem r2dAddBack_ok {s : State} {B : Addr} {Z w eA eM : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .x11 = off B eA) (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hM : eM + 8 * w ≤ Z) (sM : eA + 8 * (w + 1) ≤ eM ∨ eM + 8 * w ≤ eA) :
    WP isa addBack s fun t => ∃ c : Bool,
      wv t.mem B eA (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        wv s.mem B eA (w + 1) + (if 2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1) then wv s.mem B eM w else 0) ∧
      Outside B eA (8 * (w + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  generalize hg : decide (2 ^ 63 ≤ (word s.mem B (eA + 8 * w)).toNat) = g
  unfold addBack
  refine WP.seq (WP.mono (WP.keep [.x3, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
    t.gpr .x15 = mask g ∧ t.gpr .x16 = off B eA ∧ t.gpr .x17 = off B eM ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
    t.c = false ∧ t.mem = s.mem)
    (by brun [h11, h9, h12, h7, r2d_ofNat_shl3 (show w < 2 ^ 61 by omega_arith), hs.ld (show eA + 8 * w + 8 ≤ Z by omega_arith),
        hg]; exact (sign_mask _).trans (congrArg mask hg)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h15, h16, h17, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : AddBInv s.mem s₁ B Z eA eM g 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hc₁]; cases g <;> rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (AddBInv s.mem s₁ B Z eA eM g)
    (fun j hj t hI _ => addBStep_ok h15 hA hM sM hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7)
  have hy : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) :=
    hI.out.word (d := eA + 8 * w) (Or.inr (Nat.le_refl _)) (by omega_arith)
  refine WP.mono (WP.keep [.x3] (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (eA + 8 * w)) (word t.mem B (eA + 8 * w) + 0 + BitVec.ofNat 64 t.c.toNat))
    (by brun [hI.x16, t7, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega_arith),
      hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega_arith)]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨hm', k'⟩ => ?_
  have hs' := adcs_val (word t.mem B (eA + 8 * w)) 0 t.c
  refine ⟨decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * w)).toNat + (0 : BitVec 64).toNat + t.c.toNat), ?_, ?_,
    ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · have hT : (2 ^ (64 * (w + 1)) / 2 ≤ wv s.mem B eA (w + 1)) = (g = true) := by
      rw [← hg, sign_top, decide_eq_true_eq]
    simp only [hT]
    rw [hm', wv_writeW_top _ _ _ _ _ (by omega_arith), wv, ← hy, pow64_succ]
    exact addB_tail hI.val hs'
  · rw [hm']
    exact fun x hx' => (writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)).trans (hI.out x (by omega_arith))

end VG.Proof.Bignum.AArch64
