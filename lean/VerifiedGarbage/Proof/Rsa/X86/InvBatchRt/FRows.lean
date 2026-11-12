module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-! # The fused batches' rows on i686

A word of a row, the row's loop and its end, then `row_ok`: a row in the batch's working space writes only its outputs and `sP`, `sE`, and its
outputs, from element 0, are `⌊T / 2^30⌋ mod 2^(32 (n + 1))` for its value `T` (`rowT`).
-/

@[expose] public section

/-! ## The fused batches' rows on i686: a word

A term (`termN_ok`, `termW_ok`): the accumulator `ebx:ecx` (`:ebp`) plus the signed coefficient
times the input word, modulo `2^64` (`2^96`), from the unsigned product less `2^32` times the
word where the coefficient is negative (its mask). The word's end (`tailN_ok`, `tailW_ok`): from
an accumulator that holds `A` (`|A| < 2^63`, `2^95`), the output word `4 (A mod 2^32) + prev`, the
next `prev = (A mod 2^32) / 2^30`, and the accumulator `⌊A / 2^32⌋`.
-/

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.R2Words

/-- The accumulator, two words or three. -/
abbrev acc64 (s : State) : Nat := (s.gpr .ebx).toNat + 2 ^ 32 * (s.gpr .ecx).toNat
abbrev acc96 (s : State) : Nat := acc64 s + 2 ^ 64 * (s.gpr .ebp).toNat

/-- A word's sign mask. -/
def maskW (c : BitVec 32) : BitVec 32 := if 2 ^ 31 ≤ c.toNat then -1 else 0

theorem and_maskW (x c : BitVec 32) : (x &&& maskW c).toNat = if 2 ^ 31 ≤ c.toNat then x.toNat else 0 := by
  unfold maskW; split
  · rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
  · simp

theorem toInt_cond (c : BitVec 32) : c.toInt = if 2 ^ 31 ≤ c.toNat then (c.toNat : Int) - 2 ^ 32 else c.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := c.isLt
  split <;> split <;> first | rfl | omega

/-- A word of the working space through `r = W + x`, for `xrun`. -/
theorem ptrRead {s : State} {W : Addr} {bytes : Nat} (ws : Ws s W bytes) {r : Reg} {x d : Nat} (p : PtrAt s W r x)
    (h : x + d + 4 ≤ bytes) :
    s.gpr r = BitVec.ofNat 32 (W.toNat + x) ∧ addr (BitVec.ofNat 32 (W.toNat + x)) d = off W (x + d) ∧
      InRegions (s.rd ++ s.wr) (off W (x + d)) 4 :=
  ⟨ptr_eq p, addr_off W (by have := ws.nowrap; omega), ws_read ws h⟩

theorem termN_ok {s : State} {W : Addr} {bytes e : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) {t : Term} (hc : t.c + 4 ≤ bytes) (hm : t.m + 4 ≤ bytes) (hx : e + t.x + 4 ≤ bytes)
    (hmask : s.mem.readW (off W t.m) 32 = maskW (s.mem.readW (off W t.c) 32)) :
    WP isa (.block (termI false t)) s fun u =>
      (acc64 u : Int) = ((acc64 s : Int) + (s.mem.readW (off W t.c) 32).toInt * w32 s.mem W (e + t.x)) % 2 ^ 64 ∧
      u.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u := by
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx] (Q := fun u =>
      (acc64 u : Int) = ((acc64 s : Int) + (s.mem.readW (off W t.c) 32).toInt * w32 s.mem W (e + t.x)) % 2 ^ 64 ∧
      u.mem = s.mem) ?_ rfl) fun u ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  obtain ⟨hdi, aC, rC⟩ := ptrRead ws di (d := t.c) (by omega)
  obtain ⟨-, aM, rM⟩ := ptrRead ws di (d := t.m) (by omega)
  obtain ⟨hsi, aX, rX⟩ := ptrRead ws si (d := t.x) hx
  simp only [Nat.zero_add] at aC rC aM rM
  xrun [termI, sc, execMul, acc64, hdi, hsi, aC, rC, aM, rM, aX, rX, List.cons_append, List.nil_append, List.append_nil]
  rw [hmask]
  dsimp only [w32]
  generalize s.mem.readW (off W t.c) 32 = c
  generalize s.mem.readW (off W (e + t.x)) 32 = x
  generalize s.gpr .ebx = lo
  generalize s.gpr .ecx = hi
  have hlo := lo.isLt; have hhi := hi.isLt; have hcx := c.isLt; have hxx := x.isLt
  have ti := toInt_cond c
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    and_maskW]
  have m2 := (mul_words c x).2
  generalize hP : c.toNat * x.toNat = P at m2 ⊢
  have hcP : c.toInt * (x.toNat : Int) = P - (if 2 ^ 31 ≤ c.toNat then 2 ^ 32 * (x.toNat : Int) else 0) := by
    rw [ti]; split <;> push_cast [← hP] <;> ring
  rw [hcP]
  have hPb : P < 2 ^ 64 := by
    rw [← hP]; exact lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hcx (Nat.le_of_lt hxx) (by omega)) (by norm_num)
  have hL : (P % 2 ^ 32 : Nat) < 2 ^ 32 := Nat.mod_lt _ (by decide)
  by_cases hcar : 2 ^ 32 ≤ lo.toNat + P % 2 ^ 32 <;> simp only [hcar, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> split <;> push_cast <;> omega

theorem termW_ok {s : State} {W : Addr} {bytes e : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) {t : Term} (hc : t.c + 4 ≤ bytes) (hm : t.m + 4 ≤ bytes) (hx : e + t.x + 4 ≤ bytes)
    (hmask : s.mem.readW (off W t.m) 32 = maskW (s.mem.readW (off W t.c) 32)) :
    WP isa (.block (termI true t)) s fun u =>
      (acc96 u : Int) = ((acc96 s : Int) + (s.mem.readW (off W t.c) 32).toInt * w32 s.mem W (e + t.x)) % 2 ^ 96 ∧
      u.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .ebp] (Q := fun u =>
      (acc96 u : Int) = ((acc96 s : Int) + (s.mem.readW (off W t.c) 32).toInt * w32 s.mem W (e + t.x)) % 2 ^ 96 ∧
      u.mem = s.mem) ?_ rfl) fun u ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  obtain ⟨hdi, aC, rC⟩ := ptrRead ws di (d := t.c) (by omega)
  obtain ⟨-, aM, rM⟩ := ptrRead ws di (d := t.m) (by omega)
  obtain ⟨hsi, aX, rX⟩ := ptrRead ws si (d := t.x) hx
  simp only [Nat.zero_add] at aC rC aM rM
  xrun [termI, sc, execMul, acc96, acc64, hdi, hsi, aC, rC, aM, rM, aX, rX, List.cons_append, List.nil_append,
    List.append_nil]
  rw [hmask]
  dsimp only [w32]
  generalize s.mem.readW (off W t.c) 32 = c
  generalize s.mem.readW (off W (e + t.x)) 32 = x
  generalize s.gpr .ebx = lo
  generalize s.gpr .ecx = hi
  generalize s.gpr .ebp = top
  have hlo := lo.isLt; have hhi := hi.isLt; have htop := top.isLt; have hcx := c.isLt; have hxx := x.isLt
  have hcP : c.toInt * (x.toNat : Int) = (c.toNat * x.toNat : Nat) -
      (if 2 ^ 31 ≤ c.toNat then 2 ^ 32 * (x.toNat : Int) else 0) := by
    rw [toInt_cond c]; split <;> push_cast <;> ring
  have hPb : c.toNat * x.toNat < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hcx (Nat.le_of_lt hxx) (by omega)) (by norm_num)
  have hX := and_maskW x c
  generalize c.toNat * x.toNat = P at hcP hPb ⊢
  have hL : (BitVec.ofNat 32 P).toNat = P % 2 ^ 32 := BitVec.toNat_ofNat _ _
  have hH : (BitVec.ofNat 32 (P / 2 ^ 32)).toNat = P / 2 ^ 32 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e1 := add32_toNat lo (BitVec.ofNat 32 P)
  generalize decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 P).toNat) = c1 at e1 ⊢
  have e2 := adc32_toNat hi (BitVec.ofNat 32 (P / 2 ^ 32)) c1
  generalize decide (2 ^ 32 ≤ hi.toNat + (BitVec.ofNat 32 (P / 2 ^ 32)).toNat + c1.toNat) = c2 at e2 ⊢
  generalize hi + BitVec.ofNat 32 (P / 2 ^ 32) + BitVec.setWidth 32 (BitVec.ofBool c1) = S1 at e2 ⊢
  generalize x &&& maskW c = X at hX ⊢
  have e3 : (S1 - X).toNat + X.toNat = S1.toNat + 2 ^ 32 * (decide (S1.toNat < X.toNat)).toNat := by
    have := S1.isLt; have := X.isLt
    rw [BitVec.toNat_sub]
    by_cases h : S1.toNat < X.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true,
      Bool.toNat_false] <;> omega
  generalize decide (S1.toNat < X.toNat) = b at e3 ⊢
  have e4 : (top + 0 + BitVec.setWidth 32 (BitVec.ofBool c2) - 0 - BitVec.setWidth 32 (BitVec.ofBool b)).toNat =
      (top.toNat + c2.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
    have := Bool.toNat_le c2; have := Bool.toNat_le b
    cases c2 <;> cases b <;> simp only [BitVec.toNat_sub, BitVec.toNat_add,
      BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_true, Bool.toNat_false] <;> omega
  rw [e4, hcP]
  have := Bool.toNat_le c1; have := Bool.toNat_le c2; have := Bool.toNat_le b
  have := (lo + BitVec.ofNat 32 P).isLt; have := (S1 - X).isLt; have := S1.isLt
  rw [hL] at e1; rw [hH] at e2
  split at hX <;> push_cast <;> omega

/-- `W + e + D` modulo `2^32` as an address in the working space. -/
theorem addr_wrap (W : Addr) {e D y : Nat} (hy : (e + D) % 2 ^ 32 = y) (h : W.toNat + y < 2 ^ 32)
    (he : W.toNat + e < 2 ^ 32) (hD : D < 2 ^ 32) :
    addr (BitVec.ofNat 32 (W.toNat + e)) D = off W y := by
  have := W.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [addr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := W.toNat + e) he, Nat.mod_eq_of_lt (a := D) hD]
  have e2 : (W.toNat + e + D) % 2 ^ 32 = W.toNat + y := by omega
  rw [e2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (a := y) (by omega)]
  omega

/-- The output word of the previous element, written at byte `y` of the working space. -/
def outWord (A : Int) (prev : Nat) : BitVec 32 := BitVec.ofNat 32 (4 * (A % 2 ^ 32).toNat + prev)

theorem tailN_ok {s : State} {W : Addr} {bytes e sz o k y : Nat} (ws : Ws s W bytes) (si : PtrAt s W .esi e)
    (hy : (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = y) (hyb : y + 4 ≤ bytes) (he : e < bytes) {A : Int}
    (hA : (acc64 s : Int) = A % 2 ^ 64) (hA1 : -2 ^ 63 ≤ A) (hA2 : A < 2 ^ 63) :
    WP isa (.block (tailI false sz o k)) s fun u =>
      u.mem = s.mem.writeW (off W y) (outWord A (s.gpr .ebp).toNat) ∧
      (u.gpr .ebp).toNat = (A % 2 ^ 32).toNat / 2 ^ 30 ∧ (acc64 u : Int) = (A / 2 ^ 32) % 2 ^ 64 ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s u := by
  have nw := ws.nowrap
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .ebp] (Q := fun u =>
      u.mem = s.mem.writeW (off W y) (outWord A (s.gpr .ebp).toNat) ∧
      (u.gpr .ebp).toNat = (A % 2 ^ 32).toNat / 2 ^ 30 ∧ (acc64 u : Int) = (A / 2 ^ 32) % 2 ^ 64) ?_ rfl)
    fun u ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  have hsi := ptr_eq si
  have aY := addr_wrap W hy (by omega) (by omega) (Nat.mod_lt _ (by decide))
  have wY := ws_write ws hyb
  xrun [tailI, hsi, aY, wY, acc64, List.cons_append, List.nil_append, List.append_nil]
  simp only [acc64] at hA
  generalize s.gpr .ebx = lo at hA ⊢
  generalize s.gpr .ecx = hi at hA ⊢
  generalize s.gpr .ebp = pv
  have hlo := lo.isLt; have hhi := hi.isLt
  -- `A` from its words.
  have hl' : A % 2 ^ 32 = (lo.toNat : Int) := by omega
  have hl : (A % 2 ^ 32).toNat = lo.toNat := by rw [hl']; rfl
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [outWord, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
    omega
  · simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hl]
  · simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    by_cases hc : 2 ^ 32 ≤ hi.toNat + hi.toNat <;>
      simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> push_cast <;> omega

theorem tailW_ok {s : State} {W : Addr} {bytes e sz o k y : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) (hy : (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = y) (hyb : y + 4 ≤ bytes) (he : e < bytes)
    (hP : sP + 4 ≤ bytes) {A : Int}
    (hA : (acc96 s : Int) = A % 2 ^ 96) (hA1 : -2 ^ 95 ≤ A) (hA2 : A < 2 ^ 95) :
    WP isa (.block (tailI true sz o k)) s fun u =>
      u.mem = (s.mem.writeW (off W y) (outWord A (w32 s.mem W sP))).writeW (off W sP)
        (BitVec.ofNat 32 ((A % 2 ^ 32).toNat / 2 ^ 30)) ∧
      (acc96 u : Int) = (A / 2 ^ 32) % 2 ^ 96 ∧ Keeps [.eax, .ebx, .ecx, .ebp] s u := by
  have nw := ws.nowrap
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .ebp] (Q := fun u =>
      u.mem = (s.mem.writeW (off W y) (outWord A (w32 s.mem W sP))).writeW (off W sP)
        (BitVec.ofNat 32 ((A % 2 ^ 32).toNat / 2 ^ 30)) ∧
      (acc96 u : Int) = (A / 2 ^ 32) % 2 ^ 96) ?_ rfl)
    fun u ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hsi := ptr_eq si
  obtain ⟨hdi, aP, rP⟩ := ptrRead ws di (d := sP) (by omega)
  simp only [Nat.zero_add] at aP rP
  have wP := ws_write ws hP
  have aY := addr_wrap W hy (by omega) (by omega) (Nat.mod_lt _ (by decide))
  have wY := ws_write ws hyb
  xrun [tailI, sc, hsi, hdi, aP, rP, wP, aY, wY, acc96, acc64, List.cons_append, List.nil_append, List.append_nil]
  simp only [acc96, acc64] at hA
  generalize s.gpr .ebx = lo at hA ⊢
  generalize s.gpr .ecx = mi at hA ⊢
  generalize s.gpr .ebp = hi at hA ⊢
  have hlo := lo.isLt; have hmi := mi.isLt; have hhi := hi.isLt
  have hl' : A % 2 ^ 32 = (lo.toNat : Int) := by omega
  have hl : (A % 2 ^ 32).toNat = lo.toNat := by rw [hl']; rfl
  refine ⟨?_, ?_⟩
  · congr 1
    · congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [outWord, w32, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, hl]
      have : lo.toNat / 2 ^ 30 < 2 ^ 32 := by omega
      omega
  · simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    by_cases hc : 2 ^ 32 ≤ hi.toNat + hi.toNat <;>
      simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> push_cast <;> omega

/-- The sum of a row's terms at the pointer `W + e`. -/
def termSum (m : Mem) (W : Addr) (e : Nat) (ts : List Term) : Int :=
  (ts.map fun t => (m.readW (off W t.c) 32).toInt * (w32 m W (e + t.x) : Int)).sum

/-- What a term reads, and its mask. -/
def TermOk (m : Mem) (W : Addr) (bytes e : Nat) (t : Term) : Prop :=
  t.c + 4 ≤ bytes ∧ t.m + 4 ≤ bytes ∧ e + t.x + 4 ≤ bytes ∧ m.readW (off W t.m) 32 = maskW (m.readW (off W t.c) 32)

theorem termsN_ok {W : Addr} {bytes e : Nat} : ∀ (ts : List Term) {s : State}, Ws s W bytes → PtrAt s W .edi 0 →
    PtrAt s W .esi e → (∀ t ∈ ts, TermOk s.mem W bytes e t) →
    WP isa (.block (ts.flatMap (termI false))) s fun u =>
      (acc64 u : Int) = ((acc64 s : Int) + termSum s.mem W e ts) % 2 ^ 64 ∧ u.mem = s.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx] s u
  | [], s, _, _, _, _ => WP.block_nil ⟨by
      simp only [termSum, List.map_nil, List.sum_nil, Int.add_zero]
      have hlt : acc64 s < 2 ^ 64 := by
        have := (s.gpr .ebx).isLt; have := (s.gpr .ecx).isLt; unfold acc64; omega
      exact (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)).symm, rfl, Keeps.refl _ _⟩
  | t :: ts, s, ws, di, si, ok => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨h1, h2, h3, h4⟩ := ok t (List.mem_cons_self ..)
    refine WP.mono (termN_ok ws di si h1 h2 h3 h4) fun u ⟨au, mu, ku⟩ => ?_
    have ws' := ws.of_keeps ku
    have di' : PtrAt u W .edi 0 := by rw [PtrAt, ku.1 _ (by decide)]; exact di
    have si' : PtrAt u W .esi e := by rw [PtrAt, ku.1 _ (by decide)]; exact si
    refine WP.mono (termsN_ok ts ws' di' si' fun t' ht' => by
      rw [mu]; exact ok t' (List.mem_cons_of_mem _ ht')) fun v ⟨av, mv, kv⟩ => ⟨?_, mv.trans mu, ku.trans kv⟩
    rw [av, au, mu]
    simp only [termSum, List.map_cons, List.sum_cons]
    omega

theorem termsW_ok {W : Addr} {bytes e : Nat} : ∀ (ts : List Term) {s : State}, Ws s W bytes → PtrAt s W .edi 0 →
    PtrAt s W .esi e → (∀ t ∈ ts, TermOk s.mem W bytes e t) →
    WP isa (.block (ts.flatMap (termI true))) s fun u =>
      (acc96 u : Int) = ((acc96 s : Int) + termSum s.mem W e ts) % 2 ^ 96 ∧ u.mem = s.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u
  | [], s, _, _, _, _ => WP.block_nil ⟨by
      simp only [termSum, List.map_nil, List.sum_nil, Int.add_zero]
      have hlt : acc96 s < 2 ^ 96 := by
        have := (s.gpr .ebx).isLt; have := (s.gpr .ecx).isLt; have := (s.gpr .ebp).isLt; unfold acc96 acc64; omega
      exact (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)).symm, rfl, Keeps.refl _ _⟩
  | t :: ts, s, ws, di, si, ok => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨h1, h2, h3, h4⟩ := ok t (List.mem_cons_self ..)
    refine WP.mono (termW_ok ws di si h1 h2 h3 h4) fun u ⟨au, mu, ku⟩ => ?_
    have ws' := ws.of_keeps ku
    have di' : PtrAt u W .edi 0 := by rw [PtrAt, ku.1 _ (by decide)]; exact di
    have si' : PtrAt u W .esi e := by rw [PtrAt, ku.1 _ (by decide)]; exact si
    refine WP.mono (termsW_ok ts ws' di' si' fun t' ht' => by
      rw [mu]; exact ok t' (List.mem_cons_of_mem _ ht')) fun v ⟨av, mv, kv⟩ => ⟨?_, mv.trans mu, ku.trans kv⟩
    rw [av, au, mu]
    simp only [termSum, List.map_cons, List.sum_cons]
    omega

/-- A word of a narrow row: from the carry `C` (`acc64 = C mod 2^64`) and the previous top bits in
`ebp`, the sum `A = C + Σ cᵢ xᵢ`, its output word at `y` and the next carry and bits. -/
theorem wordN_ok {s : State} {W : Addr} {bytes e sz o k y : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) {ts : List Term}
    (ok : ∀ t ∈ ts.map (fun t => { t with x := t.x + k }), TermOk s.mem W bytes e t)
    (hy : (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = y) (hyb : y + 4 ≤ bytes) (he : e < bytes) {C : Int}
    (hC : (acc64 s : Int) = C % 2 ^ 64)
    (hA1 : -2 ^ 63 ≤ C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
    (hA2 : C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }) < 2 ^ 63) :
    WP isa (.block (wordI false ts sz o k)) s fun u =>
      u.mem = s.mem.writeW (off W y) (outWord (C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
        (s.gpr .ebp).toNat) ∧
      (u.gpr .ebp).toNat = ((C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k })) % 2 ^ 32).toNat / 2 ^ 30 ∧
      (acc64 u : Int) = ((C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k })) / 2 ^ 32) % 2 ^ 64 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  unfold wordI
  rw [WP.block_append_iff]
  refine WP.mono (termsN_ok _ ws di si ok) fun u ⟨au, mu, ku⟩ => ?_
  have ws' := ws.of_keeps ku
  have si' : PtrAt u W .esi e := by rw [PtrAt, ku.1 _ (by decide)]; exact si
  have pv : u.gpr .ebp = s.gpr .ebp := ku.1 _ (by decide)
  refine WP.mono (tailN_ok ws' si' hy hyb he (A := C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
    (by rw [au, hC]; omega) hA1 hA2) fun v ⟨mv, bv, av, kv⟩ => ⟨by rw [mv, mu, pv], bv, av, (ku.mono (by decide)).trans (kv.mono (by decide))⟩

/-- A word of a wide row: the same, the accumulator three words, the top bits at `sP`. -/
theorem wordW_ok {s : State} {W : Addr} {bytes e sz o k y : Nat} (ws : Ws s W bytes) (di : PtrAt s W .edi 0)
    (si : PtrAt s W .esi e) {ts : List Term}
    (ok : ∀ t ∈ ts.map (fun t => { t with x := t.x + k }), TermOk s.mem W bytes e t)
    (hy : (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = y) (hyb : y + 4 ≤ bytes) (he : e < bytes) (hP : sP + 4 ≤ bytes)
    {C : Int} (hC : (acc96 s : Int) = C % 2 ^ 96)
    (hA1 : -2 ^ 95 ≤ C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
    (hA2 : C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }) < 2 ^ 95) :
    WP isa (.block (wordI true ts sz o k)) s fun u =>
      u.mem = (s.mem.writeW (off W y) (outWord (C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
        (w32 s.mem W sP))).writeW (off W sP)
        (BitVec.ofNat 32 (((C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k })) % 2 ^ 32).toNat / 2 ^ 30)) ∧
      (acc96 u : Int) = ((C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k })) / 2 ^ 32) % 2 ^ 96 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  unfold wordI
  rw [WP.block_append_iff]
  refine WP.mono (termsW_ok _ ws di si ok) fun u ⟨au, mu, ku⟩ => ?_
  have ws' := ws.of_keeps ku
  have di' : PtrAt u W .edi 0 := by rw [PtrAt, ku.1 _ (by decide)]; exact di
  have si' : PtrAt u W .esi e := by rw [PtrAt, ku.1 _ (by decide)]; exact si
  refine WP.mono (tailW_ok ws' di' si' hy hyb he hP (A := C + termSum s.mem W e (ts.map fun t => { t with x := t.x + k }))
    (by rw [au, hC]; omega) hA1 hA2) fun v ⟨mv, av, kv⟩ => ⟨by rw [mv, mu], av, ku.trans (kv.mono (by decide))⟩

end VG.Proof.Rsa.X86.InvBatchRt.F

/-! ## The fused batches' rows on i686: the loop

A row runs over the elements `e₀ + sz w` of an interleaved array. `sv m W b sz N` is the number whose
words are those at `b + sz w`, `w < N`. After `N` words the accumulator holds `⌊A_N / 2^(32 N)⌋`
for `A_N = Σ cₜ sv (e₀ + xₜ) N` (`acc_next`), the top two bits of word `N - 1` of `A_N` are kept
(`prev`), and the output words so far are those of `(A_N mod 2^(32 N)) / 2^30` (`low_next`).
-/

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.R2Words

/-- The words at `b + sz w`, `w < N`, as a number. -/
def sv (m : Mem) (W : Addr) (b sz : Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => sv m W b sz N + 2 ^ (32 * N) * w32 m W (b + sz * N)

theorem sv_lt (m : Mem) (W : Addr) (b sz : Nat) : ∀ N, sv m W b sz N < 2 ^ (32 * N)
  | 0 => by simp [sv]
  | N + 1 => by
    have ih := sv_lt m W b sz N
    have hw : w32 m W (b + sz * N) < 2 ^ 32 := (m.readW _ 32).isLt
    simp only [sv]
    rw [show 32 * (N + 1) = 32 * N + 32 by omega, Nat.pow_add]
    have : 2 ^ (32 * N) * w32 m W (b + sz * N) ≤ 2 ^ (32 * N) * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (32 * N) * (2 ^ 32 - 1) = 2 ^ (32 * N) * 2 ^ 32 - 2 ^ (32 * N) := by
      rw [Nat.mul_sub, Nat.mul_one]
    have := Nat.one_le_two_pow (n := 32 * N)
    omega

theorem two_pow_pos' (k : Nat) : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)

/-- `Nat.mod_mul` for `Int`. -/
theorem int_emod_mul (x K M : Int) (hK : 0 < K) :
    x % (K * M) = x % K + K * (x / K % M) := by
  rw [Int.emod_def, Int.emod_def x K, Int.emod_def (x / K) M, ← Int.ediv_ediv_of_nonneg (Int.le_of_lt hK)]
  ring

/-- Appending a word to a sum: its quotient by the next power of `2^32`. -/
theorem acc_next (a b : Int) (N : Nat) :
    (a + 2 ^ (32 * N) * b) / 2 ^ (32 * (N + 1)) = (a / 2 ^ (32 * N) + b) / 2 ^ 32 := by
  have hk := two_pow_pos' (32 * N)
  rw [show 32 * (N + 1) = 32 * N + 32 by omega, Int.pow_add, ← Int.ediv_ediv_of_nonneg (Int.le_of_lt hk),
    Int.add_mul_ediv_left _ _ hk.ne']

/-- And its remainder. -/
theorem low_next (a b : Int) (N : Nat) :
    (a + 2 ^ (32 * N) * b) % 2 ^ (32 * (N + 1)) =
      a % 2 ^ (32 * N) + 2 ^ (32 * N) * ((a / 2 ^ (32 * N) + b) % 2 ^ 32) := by
  have hk := two_pow_pos' (32 * N)
  rw [show 32 * (N + 1) = 32 * N + 32 by omega, Int.pow_add, int_emod_mul _ _ _ hk,
    Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ hk.ne']

/-! ## The row's value -/

/-- The terms' sum over the first `N` words of the elements at `b` (inputs at `b + xₜ`). -/
def rowA (m : Mem) (W : Addr) (b sz : Nat) (ts : List Term) (N : Nat) : Int :=
  (ts.map fun t => (m.readW (off W t.c) 32).toInt * (sv m W (b + t.x) sz N : Int)).sum

theorem rowA_zero (m : Mem) (W : Addr) (b sz : Nat) (ts : List Term) : rowA m W b sz ts 0 = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [rowA, sv, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; simp

theorem rowA_succ (m : Mem) (W : Addr) (b sz : Nat) (N e k : Nat) (h : e + k = b + sz * N) :
    ∀ ts : List Term, rowA m W b sz ts (N + 1) =
      rowA m W b sz ts N + 2 ^ (32 * N) * termSum m W e (ts.map fun t => { t with x := t.x + k })
  | [] => by simp [rowA, termSum]
  | t :: ts => by
    have ih := rowA_succ m W b sz N e k h ts
    simp only [rowA, termSum, List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at ih ⊢
    rw [ih, sv, show e + (t.x + k) = b + t.x + sz * N by omega]
    push_cast; ring

/-- The sum of the coefficients' magnitudes. -/
def cB (m : Mem) (W : Addr) (ts : List Term) : Nat :=
  (ts.map fun t => (m.readW (off W t.c) 32).toInt.natAbs).sum

theorem sum_bound {α : Type} (c : α → Int) (v : α → Nat) (V : Nat) :
    ∀ l : List α, (∀ a ∈ l, v a ≤ V) →
      -((l.map fun a => (c a).natAbs).sum * V : Int) ≤ (l.map fun a => c a * (v a : Int)).sum ∧
      (l.map fun a => c a * (v a : Int)).sum ≤ ((l.map fun a => (c a).natAbs).sum * V : Int)
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨i1, i2⟩ := sum_bound c v V l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha : (v a : Int) ≤ V := by exact_mod_cast h a (List.mem_cons_self ..)
    have h0 : (0 : Int) ≤ v a := by positivity
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    generalize ((l.map fun a => (c a).natAbs).sum : Int) = X at i1 i2 ⊢
    rcases Int.le_total 0 (c a) with hc | hc
    · have e : ((c a).natAbs : Int) = c a := Int.natAbs_of_nonneg hc
      rw [e]
      have := mul_le_mul_of_nonneg_left ha hc
      constructor <;> nlinarith
    · have e : ((c a).natAbs : Int) = -c a := Int.ofNat_natAbs_of_nonpos hc
      rw [e]
      have := mul_le_mul_of_nonpos_left ha hc
      constructor <;> nlinarith

theorem termSum_bound (m : Mem) (W : Addr) (e : Nat) (ts : List Term) :
    -((cB m W ts * (2 ^ 32 - 1) : Nat) : Int) ≤ termSum m W e ts ∧
      termSum m W e ts ≤ ((cB m W ts * (2 ^ 32 - 1) : Nat) : Int) := by
  have := sum_bound (fun t : Term => (m.readW (off W t.c) 32).toInt) (fun t => w32 m W (e + t.x)) (2 ^ 32 - 1) ts
    fun t _ => by have := (m.readW (off W (e + t.x)) 32).isLt; simp only [w32]; omega
  simp only [termSum, cB]; push_cast; exact this

theorem rowA_bound (m : Mem) (W : Addr) (b sz : Nat) (ts : List Term) (N : Nat) :
    -((cB m W ts * (2 ^ (32 * N) - 1) : Nat) : Int) ≤ rowA m W b sz ts N ∧
      rowA m W b sz ts N ≤ ((cB m W ts * (2 ^ (32 * N) - 1) : Nat) : Int) := by
  have := sum_bound (fun t : Term => (m.readW (off W t.c) 32).toInt) (fun t => sv m W (b + t.x) sz N)
    (2 ^ (32 * N) - 1) ts fun t _ => by have := sv_lt m W (b + t.x) sz N; omega
  simp only [rowA, cB]; push_cast; exact this

/-- The accumulator's value at a word stays within `B 2^32`. -/
theorem word_bound {A S : Int} {B N : Nat}
    (hA : -((B * (2 ^ (32 * N) - 1) : Nat) : Int) ≤ A ∧ A ≤ ((B * (2 ^ (32 * N) - 1) : Nat) : Int))
    (hS : -((B * (2 ^ 32 - 1) : Nat) : Int) ≤ S ∧ S ≤ ((B * (2 ^ 32 - 1) : Nat) : Int)) :
    -((B * 2 ^ 32 : Nat) : Int) ≤ A / 2 ^ (32 * N) + S ∧ A / 2 ^ (32 * N) + S ≤ ((B * 2 ^ 32 : Nat) : Int) := by
  have hk := two_pow_pos' (32 * N)
  have hK : ((2 ^ (32 * N) - 1 : Nat) : Int) = 2 ^ (32 * N) - 1 := by
    have := Nat.one_le_two_pow (n := 32 * N); push_cast [Nat.cast_sub this]; rfl
  push_cast [hK] at hA hS ⊢
  have h1 : -(B : Int) ≤ A / 2 ^ (32 * N) := by
    rw [Int.le_ediv_iff_mul_le hk]; nlinarith
  have h2 : A / 2 ^ (32 * N) ≤ B := by
    rw [Int.ediv_le_iff_le_mul hk]; nlinarith
  constructor <;> nlinarith

/-! ## The output words -/

/-- The low `N` words of `A`. -/
def lw (A : Int) (N : Nat) : Nat := (A % 2 ^ (32 * N)).toNat
/-- The top two bits of word `N - 1` of `A` (`0` for `N = 0`). -/
def prevOf (A : Int) (N : Nat) : Nat := 4 * lw A N / 2 ^ (32 * N)
/-- The output words so far: those of `4 A` (the output of element `j - 1` is word `j`). -/
def outOf (A : Int) (N : Nat) : Nat := 4 * lw A N % 2 ^ (32 * N)

theorem lw_lt (A : Int) (N : Nat) : lw A N < 2 ^ (32 * N) := by
  have hk := two_pow_pos' (32 * N)
  have h1 := Int.emod_lt_of_pos A hk; have h0 := Int.emod_nonneg A hk.ne'
  unfold lw; apply Int.ofNat_lt.mp; rw [Int.toNat_of_nonneg h0]; push_cast; exact h1

theorem lw_zero (A : Int) : lw A 0 = 0 := by simp [lw]
theorem prevOf_zero (A : Int) : prevOf A 0 = 0 := by simp [prevOf, lw_zero]
theorem outOf_zero (A : Int) : outOf A 0 = 0 := by simp [outOf, Nat.mod_one]

/-- Appending a word `S` to `A`, with `t` the new word of the sum. -/
theorem lw_next (A S : Int) (N : Nat) :
    lw (A + 2 ^ (32 * N) * S) (N + 1) = lw A N + 2 ^ (32 * N) * ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat := by
  have hk := two_pow_pos' (32 * N)
  have h32 := two_pow_pos' 32
  unfold lw
  rw [low_next]
  have := Int.emod_nonneg A hk.ne'; have := Int.emod_nonneg (A / 2 ^ (32 * N) + S) h32.ne'
  have e : ((2 : Int) ^ (32 * N)) = ((2 ^ (32 * N) : Nat) : Int) := by push_cast; rfl
  rw [Int.toNat_add (by assumption) (by positivity), e, Int.toNat_mul (by positivity) (by assumption), Int.toNat_natCast]

theorem prevOf_next (A S : Int) (N : Nat) :
    prevOf (A + 2 ^ (32 * N) * S) (N + 1) = ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat / 2 ^ 30 := by
  unfold prevOf
  rw [lw_next]
  generalize ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat = t
  have hL := lw_lt A N
  generalize lw A N = L at hL ⊢
  have hk : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  rw [show 32 * (N + 1) = 32 * N + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show 4 * (L + 2 ^ (32 * N) * t) = 4 * L + 2 ^ (32 * N) * (4 * t) by ring, Nat.add_mul_div_left _ _ hk]
  have : 4 * L / 2 ^ (32 * N) < 4 := by
    rw [Nat.div_lt_iff_lt_mul hk]; omega
  generalize 4 * L / 2 ^ (32 * N) = d at this ⊢
  omega

theorem outOf_next (A S : Int) (N : Nat) :
    outOf (A + 2 ^ (32 * N) * S) (N + 1) =
      outOf A N + 2 ^ (32 * N) * ((4 * ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat + prevOf A N) % 2 ^ 32) := by
  unfold outOf prevOf
  rw [lw_next]
  generalize ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat = t
  generalize lw A N = L
  have hk : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  rw [show 32 * (N + 1) = 32 * N + 32 by omega, Nat.pow_add, Nat.mod_mul,
    show 4 * (L + 2 ^ (32 * N) * t) = 4 * L + 2 ^ (32 * N) * (4 * t) by ring, Nat.add_mul_div_left _ _ hk,
    Nat.add_mul_mod_self_left, Nat.add_comm (4 * L / _)]

/-! ## What a row writes -/

/-- `m'` agrees with `m` but on the output words at `a + o + sz j`, `j < N`, and (`wide`) at `sP`. -/
def RowFrame (W : Addr) (a sz o N : Nat) (wide : Bool) (m m' : Mem) : Prop :=
  ∀ x, (∀ j < N, ofs W x < a + o + sz * j ∨ a + o + sz * j + 4 ≤ ofs W x) →
    (wide = true → ofs W x < sP ∨ sP + 4 ≤ ofs W x) → m' x = m x

theorem RowFrame.refl (W : Addr) (a sz o : Nat) (wide : Bool) (m : Mem) : RowFrame W a sz o 0 wide m m :=
  fun _ _ _ => rfl

theorem RowFrame.out {W : Addr} {a sz o N : Nat} {wide : Bool} {m m' m'' : Mem} (h : RowFrame W a sz o N wide m m')
    (h' : Outside W (a + o + sz * N) 4 m' m'') : RowFrame W a sz o (N + 1) wide m m'' :=
  fun x hx hw => (h' x (hx N (by omega))).trans (h x (fun j hj => hx j (by omega)) hw)

theorem RowFrame.prev {W : Addr} {a sz o N : Nat} {m m' m'' : Mem} (h : RowFrame W a sz o N true m m')
    (h' : Outside W sP 4 m' m'') : RowFrame W a sz o N true m m'' :=
  fun x hx hw => (h' x (hw rfl)).trans (h x hx hw)

theorem RowFrame.w32 {W : Addr} {a sz o N : Nat} {wide : Bool} {m m' : Mem} (h : RowFrame W a sz o N wide m m')
    {d : Nat} (hd : ∀ j < N, d + 4 ≤ a + o + sz * j ∨ a + o + sz * j + 4 ≤ d)
    (hp : wide = true → d + 4 ≤ sP ∨ sP + 4 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    VG.Proof.Mont.w32 m' W d = VG.Proof.Mont.w32 m W d := by
  unfold VG.Proof.Mont.w32
  congr 1
  refine (Mem.readW_congr fun i hi => ?_).symm
  have hi' : i < 4 := by simpa using hi
  have e := ofs_off W (d := d) (i := i) (by omega)
  refine (h _ (fun j hj => ?_) (fun hw => ?_)).symm
  · rw [e]; have := hd j hj; omega
  · rw [e]; have := hp hw; omega

/-- A word of element `j'` at byte `x` of it, apart from the outputs at byte `o`. -/
theorem elem_sep {a sz o x j' : Nat} (hx : x + 4 ≤ sz) (ho : o + 4 ≤ sz) (hxo : x + 4 ≤ o ∨ o + 4 ≤ x) (j : Nat) :
    a + sz * j' + x + 4 ≤ a + o + sz * j ∨ a + o + sz * j + 4 ≤ a + sz * j' + x := by
  rcases Nat.lt_trichotomy j' j with h | rfl | h
  · have := Nat.mul_le_mul_left sz (show j' + 1 ≤ j by omega); rw [Nat.mul_succ] at this; omega
  · omega
  · have := Nat.mul_le_mul_left sz (show j + 1 ≤ j' by omega); rw [Nat.mul_succ] at this; omega

theorem sv_congr {m m' : Mem} {W : Addr} {b sz : Nat} :
    ∀ {N}, (∀ w < N, VG.Proof.Mont.w32 m' W (b + sz * w) = VG.Proof.Mont.w32 m W (b + sz * w)) →
      sv m' W b sz N = sv m W b sz N
  | 0, _ => rfl
  | N + 1, h => by
    simp only [sv]; rw [sv_congr fun w hw => h w (by omega), h N (by omega)]

/-! ## The invariant -/

/-- The accumulator, its modulus and the previous word's top bits, by the row's width. -/
def accOf (wide : Bool) (u : State) : Nat := if wide then acc96 u else acc64 u
def accM (wide : Bool) : Int := if wide then 2 ^ 96 else 2 ^ 64
def prevAt (wide : Bool) (W : Addr) (u : State) : Nat :=
  if wide then VG.Proof.Mont.w32 u.mem W sP else (u.gpr .ebp).toNat

/-- What a row needs: its elements from `a` (the scratch element) to element `n + 1`, the outputs
at byte `o` of each, its terms' coefficients and masks in the header below `a`. -/
structure RowOk (s₀ : State) (W : Addr) (bytes a sz o n : Nat) (ts : List Term) (wide : Bool) : Prop where
  ws : Ws s₀ W bytes
  di : PtrAt s₀ W .edi 0
  ho : o + 4 ≤ sz
  fits : a + sz * (n + 2) < bytes
  hP : wide = true → sP + 4 ≤ a
  terms : ∀ t ∈ ts, t.c + 4 ≤ a ∧ t.m + 4 ≤ a ∧ t.x + 4 ≤ sz ∧ (t.x + 4 ≤ o ∨ o + 4 ≤ t.x) ∧
    (wide = true → (t.c + 4 ≤ sP ∨ sP + 4 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 4 ≤ t.m)) ∧
    s₀.mem.readW (off W t.m) 32 = maskW (s₀.mem.readW (off W t.c) 32)
  bound : cB s₀.mem W ts * 2 ^ 32 ≤ if wide then 2 ^ 94 else 2 ^ 62

/-- A row after its first `N` words. -/
structure RowInv (s₀ : State) (W : Addr) (a sz o : Nat) (ts : List Term) (wide : Bool) (N : Nat) (u : State) :
    Prop where
  keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ u
  frame : RowFrame W a sz o N wide s₀.mem u.mem
  acc : (accOf wide u : Int) = rowA s₀.mem W (a + sz) sz ts N / 2 ^ (32 * N) % accM wide
  prev : prevAt wide W u = prevOf (rowA s₀.mem W (a + sz) sz ts N) N
  out : sv u.mem W (a + o) sz N = outOf (rowA s₀.mem W (a + sz) sz ts N) N

theorem mul_step {sz j N : Nat} (h : j < N) : sz * j + sz ≤ sz * N := by
  have := Nat.mul_le_mul_left sz (show j + 1 ≤ N by omega); rwa [Nat.mul_succ] at this

theorem mul_mono {sz j N : Nat} (h : j ≤ N) : sz * j ≤ sz * N := Nat.mul_le_mul_left sz h

variable {s₀ : State} {W : Addr} {bytes a sz o n : Nat} {ts : List Term} {wide : Bool}

/-- A header word, unchanged by the row so far. -/
theorem RowOk.hdr {N : Nat} {m : Mem} (R : RowOk s₀ W bytes a sz o n ts wide)
    (F : RowFrame W a sz o N wide s₀.mem m) {d : Nat} (hd : d + 4 ≤ a)
    (hp : wide = true → d + 4 ≤ sP ∨ sP + 4 ≤ d) : m.readW (off W d) 32 = s₀.mem.readW (off W d) 32 :=
  BitVec.eq_of_toNat_eq (F.w32 (fun j _ => by omega) hp (by have := R.ws.nowrap; have := R.fits; omega))

/-- An input word of element `j` (`1 ≤ j ≤ n + 1`), unchanged by the row so far. -/
theorem RowOk.input {N : Nat} {m : Mem} (R : RowOk s₀ W bytes a sz o n ts wide)
    (F : RowFrame W a sz o N wide s₀.mem m) {t : Term} (ht : t ∈ ts) {j : Nat} (hj : 1 ≤ j) (hjn : j ≤ n + 1) :
    VG.Proof.Mont.w32 m W (a + sz * j + t.x) = VG.Proof.Mont.w32 s₀.mem W (a + sz * j + t.x) := by
  obtain ⟨-, -, hx, hxo, -⟩ := R.terms t ht
  have := R.ho; have := R.fits; have := R.ws.nowrap
  have := mul_step (sz := sz) (show j < n + 2 by omega)
  refine F.w32 (fun j' _ => elem_sep hx R.ho hxo j') (fun hw => ?_) (by omega)
  have := R.hP hw
  have := mul_mono (sz := sz) hj; omega

theorem termSum_congr {m m' : Mem} {W : Addr} {e : Nat} :
    ∀ {ts : List Term}, (∀ t ∈ ts, m'.readW (off W t.c) 32 = m.readW (off W t.c) 32 ∧
      VG.Proof.Mont.w32 m' W (e + t.x) = VG.Proof.Mont.w32 m W (e + t.x)) → termSum m' W e ts = termSum m W e ts
  | [], _ => rfl
  | t :: ts, h => by
    have ih := termSum_congr (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    obtain ⟨h1, h2⟩ := h t (List.mem_cons_self ..)
    simp only [termSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, h1, h2]

theorem cB_map (m : Mem) (W : Addr) (k : Nat) (ts : List Term) :
    cB m W (ts.map fun t => { t with x := t.x + k }) = cB m W ts := by
  simp only [cB, List.map_map, Function.comp_def]

/-- The facts a word of the row needs, at the state `u` after `N` words, with `esi = W + e` and
the word's inputs at `e + k` (`= a + sz (N + 1)`). -/
theorem wordFacts {N e k : Nat} {u : State} (R : RowOk s₀ W bytes a sz o n ts wide)
    (I : RowInv s₀ W a sz o ts wide N u) (hN : N ≤ n) (hek : e + k = a + sz + sz * N) :
    Ws u W bytes ∧ PtrAt u W .edi 0 ∧
    (∀ t ∈ ts.map (fun t => { t with x := t.x + k }), TermOk u.mem W bytes e t) ∧
    (e + (neg sz + o + k) % 2 ^ 32) % 2 ^ 32 = a + o + sz * N ∧ a + o + sz * N + 4 ≤ bytes ∧ e < bytes ∧
    termSum u.mem W e (ts.map fun t => { t with x := t.x + k }) =
      termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) ∧
    rowA s₀.mem W (a + sz) sz ts (N + 1) = rowA s₀.mem W (a + sz) sz ts N +
      2 ^ (32 * N) * termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) ∧
    -((cB s₀.mem W ts * 2 ^ 32 : Nat) : Int) ≤ rowA s₀.mem W (a + sz) sz ts N / 2 ^ (32 * N) +
      termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) ∧
    rowA s₀.mem W (a + sz) sz ts N / 2 ^ (32 * N) +
      termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) ≤ ((cB s₀.mem W ts * 2 ^ 32 : Nat) : Int) := by
  have nw := R.ws.nowrap; have fits := R.fits; have ho := R.ho
  have m1 := mul_step (sz := sz) (show N < n + 1 by omega)
  have m2 := mul_step (sz := sz) (show n + 1 < n + 2 by omega)
  have m3 := mul_mono (sz := sz) (show n + 1 ≤ n + 2 by omega)
  have hel : ∀ t : Term, e + t.x + k = a + sz * (N + 1) + t.x := fun t => by rw [Nat.mul_succ]; omega
  have inp : ∀ t ∈ ts, VG.Proof.Mont.w32 u.mem W (e + (t.x + k)) = VG.Proof.Mont.w32 s₀.mem W (e + (t.x + k)) :=
    fun t ht => by
      rw [← Nat.add_assoc, hel t]
      exact R.input I.frame ht (by omega) (by omega)
  have hdr : ∀ t ∈ ts, u.mem.readW (off W t.c) 32 = s₀.mem.readW (off W t.c) 32 ∧
      u.mem.readW (off W t.m) 32 = s₀.mem.readW (off W t.m) 32 := fun t ht => by
    obtain ⟨hc, hm, -, -, hw, -⟩ := R.terms t ht
    exact ⟨R.hdr I.frame hc fun h => (hw h).1, R.hdr I.frame hm fun h => (hw h).2⟩
  have ts_eq : termSum u.mem W e (ts.map fun t => { t with x := t.x + k }) =
      termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) := by
    refine termSum_congr fun t ht => ?_
    obtain ⟨t0, h0, rfl⟩ := List.mem_map.mp ht
    exact ⟨(hdr t0 h0).1, inp t0 h0⟩
  have hsucc := rowA_succ s₀.mem W (a + sz) sz N e k hek ts
  have wb := word_bound (rowA_bound s₀.mem W (a + sz) sz ts N)
    (by have := termSum_bound s₀.mem W e (ts.map fun t => { t with x := t.x + k }); rwa [cB_map] at this)
  refine ⟨R.ws.of_keeps I.keep, by rw [PtrAt, I.keep.1 _ (by decide)]; exact R.di, ?_, ?_, ?_, ?_, ts_eq, hsucc,
    wb.1, wb.2⟩
  · intro t ht
    obtain ⟨t0, h0, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hc, hm, hx, -, -, hmask⟩ := R.terms t0 h0
    refine ⟨show t0.c + 4 ≤ bytes by omega, show t0.m + 4 ≤ bytes by omega, ?_, ?_⟩
    · show e + (t0.x + k) + 4 ≤ bytes
      rw [← Nat.add_assoc, hel t0, Nat.mul_succ]; omega
    · show u.mem.readW (off W t0.m) 32 = maskW (u.mem.readW (off W t0.c) 32)
      rw [(hdr t0 h0).1, (hdr t0 h0).2, hmask]
  · unfold neg
    generalize sz * N = q at *
    omega
  · omega
  · omega

theorem outWord_toNat (A : Int) (p : Nat) : (outWord A p).toNat = (4 * (A % 2 ^ 32).toNat + p) % 2 ^ 32 := by
  simp only [outWord, BitVec.toNat_ofNat]

/-- A word of the row: from `N` words to `N + 1`. -/
theorem wordStep_ok {N e k : Nat} {u : State} (R : RowOk s₀ W bytes a sz o n ts wide)
    (I : RowInv s₀ W a sz o ts wide N u) (hN : N ≤ n) (hek : e + k = a + sz + sz * N)
    (si : PtrAt u W .esi e) :
    WP isa (.block (wordI wide ts sz o k)) u fun v =>
      RowInv s₀ W a sz o ts wide (N + 1) v ∧ v.gpr .esi = u.gpr .esi := by
  obtain ⟨wsu, diu, ok, hy, hyb, he, tsq, hsucc, b1, b2⟩ := wordFacts R I hN hek
  have nw := R.ws.nowrap; have fits := R.fits; have ho := R.ho
  have m1 := mul_step (sz := sz) (show N < n + 1 by omega)
  have m2 := mul_step (sz := sz) (show n + 1 < n + 2 by omega)
  have bound := R.bound
  have iacc := I.acc; have iprev := I.prev; have iout := I.out
  generalize hA : rowA s₀.mem W (a + sz) sz ts N = A at iacc iprev iout hsucc b1 b2
  generalize hS : termSum s₀.mem W e (ts.map fun t => { t with x := t.x + k }) = S at tsq hsucc b1 b2
  have earlier : ∀ {m : Mem} {d : Nat} (v : BitVec 32), (∀ j < N, a + o + sz * j + 4 ≤ d) → d + 4 ≤ bytes →
      sv (m.writeW (off W d) v) W (a + o) sz N = sv m W (a + o) sz N := fun v hd hdb =>
    sv_congr fun w hw => w32_write_ne (size := bytes) nw hdb (by have := mul_step (sz := sz) hw; omega)
      (.inl (hd w hw)) v
  have outs : ∀ j < N, a + o + sz * j + 4 ≤ a + o + sz * N := fun j hj => by
    have := mul_step (sz := sz) hj; omega
  cases wide with
  | false =>
    simp only [accOf, accM, prevAt, Bool.false_eq_true, ↓reduceIte] at iacc iprev
    have hacc : (acc64 u : Int) = (A / 2 ^ (32 * N)) % 2 ^ 64 := iacc
    simp only [Bool.false_eq_true, ↓reduceIte] at bound
    refine WP.mono (wordN_ok wsu diu si ok hy hyb he hacc (by rw [tsq]; omega) (by rw [tsq]; omega))
      fun v ⟨mv, bv, av, kv⟩ => ⟨⟨I.keep.trans (kv.mono (by decide)), ?_, ?_, ?_, ?_⟩, kv.1 _ (by decide)⟩
    · rw [mv]; exact I.frame.out (writeW32_outside _ _ _ (by omega))
    · show (acc64 v : Int) = _
      rw [av, tsq, hsucc, acc_next]; rfl
    · show (v.gpr .ebp).toNat = _
      rw [bv, tsq, hsucc, prevOf_next]
    · simp only [sv]
      rw [mv, earlier _ outs (by omega), w32_write_self, iout, outWord_toNat, tsq, hsucc, outOf_next, iprev]
  | true =>
    simp only [accOf, accM, prevAt, ↓reduceIte] at iacc iprev
    have hacc : (acc96 u : Int) = (A / 2 ^ (32 * N)) % 2 ^ 96 := iacc
    simp only [↓reduceIte] at bound
    have hP := R.hP rfl
    refine WP.mono (wordW_ok wsu diu si ok hy hyb he (by omega) hacc (by rw [tsq]; omega) (by rw [tsq]; omega))
      fun v ⟨mv, av, kv⟩ => ⟨⟨I.keep.trans (kv.mono (by decide)), ?_, ?_, ?_, ?_⟩, kv.1 _ (by decide)⟩
    · rw [mv]
      exact (I.frame.out (writeW32_outside _ _ _ (by omega))).prev (writeW32_outside _ _ _ (by omega))
    · show (acc96 v : Int) = _
      rw [av, tsq, hsucc, acc_next]; rfl
    · show VG.Proof.Mont.w32 v.mem W sP = _
      rw [mv, w32_write_self, tsq, hsucc, prevOf_next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have : ((A / 2 ^ (32 * N) + S) % 2 ^ 32).toNat < 2 ^ 32 := by
        have := Int.emod_lt_of_pos (A / 2 ^ (32 * N) + S) (two_pow_pos' 32); omega
      omega
    · simp only [sv]
      have hsp : ∀ {m : Mem} (v : BitVec 32), sv (m.writeW (off W sP) v) W (a + o) sz N = sv m W (a + o) sz N :=
        fun v => sv_congr fun w hw => w32_write_ne (size := bytes) nw (by omega)
          (by have := mul_step (sz := sz) hw; omega) (.inr (by omega)) v
      rw [mv, hsp, earlier _ outs (by omega), w32_write_ne (size := bytes) nw (by omega) (by omega) (.inr (by omega)),
        w32_write_self, iout, outWord_toNat, tsq, hsucc, outOf_next, iprev]

/-- The loop's step and test: `esi += d`, against the end in `sE`. -/
theorem advCmp_ok {v : State} {W : Addr} {bytes e d E : Nat} (ws : Ws v W bytes) (di : PtrAt v W .edi 0)
    (si : PtrAt v W .esi e) (hE : v.mem.readW (off W sE) 32 = BitVec.ofNat 32 (W.toNat + E)) (hsE : sE + 4 ≤ bytes)
    (hd : e + d < bytes) (hEb : E < bytes) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 d)), .alu .cmp .esi (.mem (sc sE))]) v fun w =>
      PtrAt w W .esi (e + d) ∧ w.mem = v.mem ∧ Keeps [.esi] v w ∧ eval .ne w = some (!decide (e + d = E)) := by
  have nw := ws.nowrap
  refine WP.mono (WP.keeps [.esi] (Q := fun w =>
      (w.gpr .esi).toNat = (W.toNat + (e + d)) % 2 ^ 32 ∧ w.mem = v.mem ∧ w.zf = some (decide (e + d = E))) ?_ rfl)
    fun w ⟨h, k⟩ => ⟨h.1, h.2.1, k, by change w.zf.map (!·) = _; rw [h.2.2]; rfl⟩
  have hsi := ptr_eq si
  obtain ⟨hdi, aE, rE⟩ := ptrRead ws di (d := sE) (by omega)
  simp only [Nat.zero_add] at aE rE
  xrun [sc, hsi, hdi, aE, rE, hE]
  have := W.isLt
  refine ⟨by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, ?_⟩
  rw [Bool.eq_iff_iff]
  have h1 : (W.toNat + e) % 2 ^ 32 = W.toNat + e := Nat.mod_eq_of_lt (by omega)
  have h2 : d % 2 ^ 32 = d := Nat.mod_eq_of_lt (by omega)
  have h3 : (W.toNat + E) % 2 ^ 32 = W.toNat + E := Nat.mod_eq_of_lt (by omega)
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add,
    BitVec.toNat_ofNat, h1, h2, h3]
  generalize W.toNat = w at *
  rw [show BitVec.toNat (0 : BitVec 32) = 0 from rfl]
  omega

/-- The invariant holds on with only `esi` and the flags changed. -/
theorem RowInv.of_esi {N : Nat} {v w : State} (I : RowInv s₀ W a sz o ts wide N v) (k : Keeps [.esi] v w)
    (m : w.mem = v.mem) : RowInv s₀ W a sz o ts wide N w := by
  have hb : w.gpr .ebx = v.gpr .ebx := k.1 _ (by decide)
  have hc : w.gpr .ecx = v.gpr .ecx := k.1 _ (by decide)
  have hp : w.gpr .ebp = v.gpr .ebp := k.1 _ (by decide)
  refine ⟨I.keep.trans (k.mono (by decide)), m ▸ I.frame, ?_, ?_, m ▸ I.out⟩
  · have := I.acc; simp only [accOf, acc96, acc64] at this ⊢; rw [hb, hc, hp]; exact this
  · have := I.prev; simp only [prevAt] at this ⊢; rw [hp, m]; exact this

/-- The row's loop: pairs of words up to word `n` (`n` even). -/
theorem rowLoop_ok {u₀ : State} (R : RowOk s₀ W bytes a sz o n ts wide) (hn : 0 < n) (he : n % 2 = 0)
    (I₀ : RowInv s₀ W a sz o ts wide 0 u₀) (si₀ : PtrAt u₀ W .esi (a + sz))
    (hsE : sE + 4 ≤ a) (hE : s₀.mem.readW (off W sE) 32 = BitVec.ofNat 32 (W.toNat + (a + sz + sz * n))) :
    WP isa (.loop (.block (rowStep wide ts sz o)) .ne) u₀ fun v =>
      RowInv s₀ W a sz o ts wide n v ∧ PtrAt v W .esi (a + sz + sz * n) := by
  have nw := R.ws.nowrap; have fits := R.fits; have ho := R.ho
  have mn := mul_step (sz := sz) (show n < n + 1 by omega)
  have mn2 := mul_step (sz := sz) (show n + 1 < n + 2 by omega)
  refine WP.loop (M := isa) (fun rem v => ∃ i, rem = n / 2 - i ∧ 2 * i < n ∧
      RowInv s₀ W a sz o ts wide (2 * i) v ∧ PtrAt v W .esi (a + sz + sz * (2 * i))) ?_ (n / 2) u₀
    ⟨0, by omega, by omega, I₀, by simpa using si₀⟩
  rintro rem v ⟨i, rfl, hi, I, si⟩
  unfold rowStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wordStep_ok R I (by omega) (by omega) si) fun v₁ ⟨I₁, e₁⟩ => ?_
  have si₁ : PtrAt v₁ W .esi (a + sz + sz * (2 * i)) := by rw [PtrAt, e₁]; exact si
  refine WP.mono (wordStep_ok R I₁ (by omega) (by rw [Nat.mul_succ]; omega) si₁) fun v₂ ⟨I₂, e₂⟩ => ?_
  have si₂ : PtrAt v₂ W .esi (a + sz + sz * (2 * i)) := by rw [PtrAt, e₂]; exact si₁
  have ws₂ := R.ws.of_keeps I₂.keep
  have di₂ : PtrAt v₂ W .edi 0 := by rw [PtrAt, I₂.keep.1 _ (by decide)]; exact R.di
  have hE₂ : v₂.mem.readW (off W sE) 32 = BitVec.ofNat 32 (W.toNat + (a + sz + sz * n)) := by
    rw [R.hdr I₂.frame hsE (fun _ => by decide), hE]
  have mi := mul_mono (sz := sz) (show 2 * i + 2 ≤ n by omega)
  have he' : a + sz + sz * (2 * i) + 2 * sz = a + sz + sz * (2 * i + 2) := by rw [Nat.mul_add]; omega
  refine WP.mono (advCmp_ok ws₂ di₂ si₂ hE₂ (by omega) (by omega) (by omega)) fun w ⟨siw, mw, kw, ew⟩ => ?_
  have Iw := I₂.of_esi kw mw
  rw [he'] at siw ew
  by_cases last : 2 * i + 2 = n
  · left
    refine ⟨by change eval .ne w = _; rw [ew]; simp [last], ?_, ?_⟩
    · rw [← last]; exact Iw
    · rw [← last]; exact siw
  · right
    have ne : a + sz + sz * (2 * i + 2) ≠ a + sz + sz * n := fun h =>
      last (Nat.eq_of_mul_eq_mul_left (show 0 < sz by omega) (by omega))
    refine ⟨by change eval .ne w = _; rw [ew, decide_eq_false ne]; rfl, n / 2 - (i + 1), by omega, i + 1, rfl, by omega, ?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]; exact Iw
    · rw [show 2 * (i + 1) = 2 * i + 2 by omega]; exact siw

/-! ## The row's end -/

theorem fixArith (B X C : BitVec 32) :
    ((B - ((0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤ X.toNat + X.toNat)))) &&& C)).toNat : Int) =
      ((B.toNat : Int) - if 2 ^ 31 ≤ X.toNat then C.toInt else 0) % 2 ^ 32 := by
  have hB := B.isLt; have hC := C.isLt
  by_cases h : 2 ^ 31 ≤ X.toNat
  · rw [decide_eq_true (by omega),
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true)) = BitVec.allOnes 32 by decide, BitVec.allOnes_and,
      BitVec.toNat_sub, toInt_cond C]
    simp only [h, ↓reduceIte]
    split <;> omega
  · rw [decide_eq_false (by omega),
      show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false)) = 0#32 by decide, BitVec.zero_and, BitVec.sub_zero]
    simp only [h, ↓reduceIte]
    omega

/-- A signed term's correction: its coefficient where its top word (at byte `y`) is negative. -/
theorem topFix_ok {u : State} {W : Addr} {bytes E y : Nat} (ws : Ws u W bytes) (di : PtrAt u W .edi 0)
    (si : PtrAt u W .esi E) {t : Term} (hy : (E + (neg sz + t.x)) % 2 ^ 32 = y) (hD : neg sz + t.x < 2 ^ 32)
    (hyb : y + 4 ≤ bytes) (hE : E < bytes) (hc : t.c + 4 ≤ bytes) :
    WP isa (.block (topFix wide sz t)) u fun v =>
      ((v.gpr .ebx).toNat : Int) = (((u.gpr .ebx).toNat : Int) -
        (if 2 ^ 31 ≤ VG.Proof.Mont.w32 u.mem W y then (u.mem.readW (off W t.c) 32).toInt else 0)) % 2 ^ 32 ∧
      v.mem = u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] u v ∧ (wide = false → v.gpr .ebp = u.gpr .ebp) := by
  have nw := ws.nowrap
  have hsi := ptr_eq si
  obtain ⟨hdi, aC, rC⟩ := ptrRead ws di (d := t.c) (by omega)
  simp only [Nat.zero_add] at aC rC
  have aY := addr_wrap W hy (by omega) (by omega) hD
  have rY := ws_read ws hyb
  cases wide with
  | false =>
    refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx] (Q := fun v =>
        ((v.gpr .ebx).toNat : Int) = (((u.gpr .ebx).toNat : Int) -
          (if 2 ^ 31 ≤ VG.Proof.Mont.w32 u.mem W y then (u.mem.readW (off W t.c) 32).toInt else 0)) % 2 ^ 32 ∧
        v.mem = u.mem) ?_ rfl) fun v ⟨h, k⟩ => ⟨h.1, h.2, k.mono (by decide), fun _ => k.1 _ (by decide)⟩
    xrun [topFix, signEax, sc, hsi, hdi, aC, rC, aY, rY, List.cons_append, List.nil_append, List.append_nil]
    exact fixArith (u.gpr .ebx) (u.mem.readW (off W y) 32) (u.mem.readW (off W t.c) 32)
  | true =>
    refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .ebp] (Q := fun v =>
        ((v.gpr .ebx).toNat : Int) = (((u.gpr .ebx).toNat : Int) -
          (if 2 ^ 31 ≤ VG.Proof.Mont.w32 u.mem W y then (u.mem.readW (off W t.c) 32).toInt else 0)) % 2 ^ 32 ∧
        v.mem = u.mem) ?_ rfl) fun v ⟨h, k⟩ => ⟨h.1, h.2, k, fun h => nomatch h⟩
    xrun [topFix, signEax, sc, hsi, hdi, aC, rC, aY, rY, List.cons_append, List.nil_append, List.append_nil]
    exact fixArith (u.gpr .ebx) (u.mem.readW (off W y) 32) (u.mem.readW (off W t.c) 32)

/-- The signed terms' corrections: each coefficient whose input's top word (at `b + x`) is
negative. -/
def topF (m : Mem) (W : Addr) (b : Nat) (signed : List Term) : Int :=
  (signed.map fun t => if 2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + t.x) then (m.readW (off W t.c) 32).toInt else 0).sum

theorem topFixes_ok {W : Addr} {bytes b : Nat} (hsz : sz ≤ b) (hbW : W.toNat + b + sz < 2 ^ 32) :
    ∀ (signed : List Term) {u : State}, Ws u W bytes → PtrAt u W .edi 0 → PtrAt u W .esi (b + sz) →
      (∀ t ∈ signed, t.x + 4 ≤ sz ∧ b + t.x + 4 ≤ bytes ∧ t.c + 4 ≤ bytes) → b + sz < bytes →
      WP isa (.block (signed.flatMap (topFix wide sz))) u fun v =>
        ((v.gpr .ebx).toNat : Int) = (((u.gpr .ebx).toNat : Int) - topF u.mem W b signed) % 2 ^ 32 ∧
        v.mem = u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] u v ∧ (wide = false → v.gpr .ebp = u.gpr .ebp)
  | [], u, _, _, _, _, _ => WP.block_nil ⟨by
      simp only [topF, List.map_nil, List.sum_nil, Int.sub_zero]
      have := (u.gpr .ebx).isLt
      exact (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast this)).symm, rfl, Keeps.refl _ _, fun _ => rfl⟩
  | t :: ts, u, ws, di, si, ok, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨h1, h2, h3⟩ := ok t (List.mem_cons_self ..)
    refine WP.mono (topFix_ok ws di si (y := b + t.x) (by unfold neg; omega) (by unfold neg; omega) h2 hb h3)
      fun u' ⟨bu, mu, ku, pu⟩ => ?_
    have ws' := ws.of_keeps ku
    have di' : PtrAt u' W .edi 0 := by rw [PtrAt, ku.1 _ (by decide)]; exact di
    have si' : PtrAt u' W .esi (b + sz) := by rw [PtrAt, ku.1 _ (by decide)]; exact si
    refine WP.mono (topFixes_ok hsz hbW ts ws' di' si' (fun t' ht' => ok t' (List.mem_cons_of_mem _ ht')) hb)
      fun v ⟨bv, mv, kv, pv⟩ => ⟨?_, mv.trans mu, ku.trans kv, fun h => (pv h).trans (pu h)⟩
    rw [bv, bu, mu]
    simp only [topF, List.map_cons, List.sum_cons]
    omega

/-- The last output word: `4 ebx + prev`, at byte `o` of the element below `esi`. -/
theorem lastWord_ok {u : State} {W : Addr} {bytes E y : Nat} (ws : Ws u W bytes) (di : PtrAt u W .edi 0)
    (si : PtrAt u W .esi E) (hy : (E + (neg sz + o)) % 2 ^ 32 = y) (hD : neg sz + o < 2 ^ 32)
    (hyb : y + 4 ≤ bytes) (hE : E < bytes) (hP : wide = true → sP + 4 ≤ bytes) :
    WP isa (.block (([.alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx)] : List Instr) ++
        (if wide then [.alu .add .ebx (.mem (sc sP))] else [.alu .add .ebx (.reg .ebp)]) ++
        ([.store (at_ .esi (neg sz + o)) .ebx] : List Instr))) u fun v =>
      v.mem = u.mem.writeW (off W y) (BitVec.ofNat 32 (4 * (u.gpr .ebx).toNat + prevAt wide W u)) ∧
      Keeps [.ebx] u v := by
  have nw := ws.nowrap
  have hsi := ptr_eq si
  have aY := addr_wrap W hy (by omega) (by omega) hD
  have wY := ws_write ws hyb
  cases wide with
  | false =>
    refine WP.mono (WP.keeps [.ebx] (Q := fun v =>
      v.mem = u.mem.writeW (off W y) (BitVec.ofNat 32 (4 * (u.gpr .ebx).toNat + prevAt false W u))) ?_ rfl)
      fun v ⟨h, k⟩ => ⟨h, k⟩
    xrun [hsi, aY, wY, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true, ↓reduceIte]
    simp only [prevAt, Bool.false_eq_true, ↓reduceIte]
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  | true =>
    obtain ⟨hdi, aP, rP⟩ := ptrRead ws di (d := sP) (by have := hP rfl; omega)
    simp only [Nat.zero_add] at aP rP
    refine WP.mono (WP.keeps [.ebx] (Q := fun v =>
      v.mem = u.mem.writeW (off W y) (BitVec.ofNat 32 (4 * (u.gpr .ebx).toNat + prevAt true W u))) ?_ rfl)
      fun v ⟨h, k⟩ => ⟨h, k⟩
    xrun [sc, hdi, aP, rP, hsi, aY, wY, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte]
    simp only [prevAt, ↓reduceIte]
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.Mont.w32]; omega

/-- `esi += d`. -/
theorem addEsi_ok {v : State} {W : Addr} {e d : Nat} (si : PtrAt v W .esi e) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 d))]) v fun w =>
      PtrAt w W .esi (e + d) ∧ w.mem = v.mem ∧ Keeps [.esi] v w := by
  refine WP.mono (WP.keeps [.esi] (Q := fun w =>
      (w.gpr .esi).toNat = (W.toNat + (e + d)) % 2 ^ 32 ∧ w.mem = v.mem) ?_ rfl) fun w ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hsi := ptr_eq si
  xrun [hsi]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem topF_congr {m m' : Mem} {W : Addr} {b : Nat} :
    ∀ {signed : List Term}, (∀ t ∈ signed, m'.readW (off W t.c) 32 = m.readW (off W t.c) 32 ∧
      VG.Proof.Mont.w32 m' W (b + t.x) = VG.Proof.Mont.w32 m W (b + t.x)) → topF m' W b signed = topF m W b signed
  | [], _ => by simp only [topF, List.map_nil]
  | t :: ts, h => by
    have ih := topF_congr (signed := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    obtain ⟨h1, h2⟩ := h t (List.mem_cons_self ..)
    simp only [topF, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, h1, h2]

/-- The row's value: the terms over `n + 1` words, the signed ones sign-extended. -/
def rowT (m : Mem) (W : Addr) (a sz n : Nat) (ts signed : List Term) : Int :=
  rowA m W (a + sz) sz ts (n + 1) - 2 ^ (32 * (n + 1)) * topF m W (a + sz * (n + 1)) signed

/-- A row, done: its `n + 2` output words, from the scratch element's. -/
structure RowDone (s₀ : State) (W : Addr) (a sz o n : Nat) (ts signed : List Term) (wide : Bool) (v : State) :
    Prop where
  keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ v
  frame : RowFrame W a sz o (n + 2) wide s₀.mem v.mem
  out : sv v.mem W (a + o) sz (n + 2) = outOf (rowT s₀.mem W a sz n ts signed) (n + 2)

theorem ebx_of_acc {wide : Bool} {u : State} {C : Int} (h : (accOf wide u : Int) = C % accM wide) :
    ((u.gpr .ebx).toNat : Int) = C % 2 ^ 32 := by
  have hb := (u.gpr .ebx).isLt
  have e : ((u.gpr .ebx).toNat : Int) = (accOf wide u : Int) % 2 ^ 32 := by
    cases wide <;> simp only [accOf, acc96, acc64, Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> omega
  rw [e, h]
  cases wide <;> simp only [accM, Bool.false_eq_true, ↓reduceIte] <;>
    exact Int.emod_emod_of_dvd _ (by decide)

/-- The row's end: word `n`, the signed terms' corrections and the last output word. -/
theorem rowEnd_ok {u : State} (R : RowOk s₀ W bytes a sz o n ts wide)
    (I : RowInv s₀ W a sz o ts wide n u) (si : PtrAt u W .esi (a + sz + sz * n)) {signed : List Term}
    (hsg : ∀ t ∈ signed, t ∈ ts) {is : List Instr} {Q : State → Prop}
    (k : ∀ v, RowDone s₀ W a sz o n ts signed wide v → WP isa (.block is) v Q) :
    WP isa (.block (wordI wide ts sz o 0 ++ ([.alu .add .esi (.imm (BitVec.ofNat 32 sz))] : List Instr) ++
      signed.flatMap (topFix wide sz) ++ ([.alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx)] : List Instr) ++
      (if wide then [.alu .add .ebx (.mem (sc sP))] else [.alu .add .ebx (.reg .ebp)]) ++
      ([.store (at_ .esi (neg sz + o)) .ebx] : List Instr) ++ is)) u Q := by
  have nw := R.ws.nowrap; have fits := R.fits; have ho := R.ho
  have m1 := mul_step (sz := sz) (show n < n + 1 by omega)
  have m2 := mul_step (sz := sz) (show n + 1 < n + 2 by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wordStep_ok R I (Nat.le_refl _) (by omega) si) fun u₁ ⟨I₁, e₁⟩ => ?_
  have si₁ : PtrAt u₁ W .esi (a + sz + sz * n) := by rw [PtrAt, e₁]; exact si
  rw [WP.block_append_iff]
  refine WP.mono (addEsi_ok si₁) fun u₂ ⟨si₂, mu₂, ku₂⟩ => ?_
  have I₂ := I₁.of_esi ku₂ mu₂
  have hb : a + sz + sz * n + sz = a + sz * (n + 1) + sz := by rw [Nat.mul_succ]; omega
  rw [hb] at si₂
  have ws₂ := R.ws.of_keeps I₂.keep
  have di₂ : PtrAt u₂ W .edi 0 := by rw [PtrAt, I₂.keep.1 _ (by decide)]; exact R.di
  have tok : ∀ t ∈ signed, t.x + 4 ≤ sz ∧ a + sz * (n + 1) + t.x + 4 ≤ bytes ∧ t.c + 4 ≤ bytes := fun t ht => by
    obtain ⟨hc, -, hx, -⟩ := R.terms t (hsg t ht)
    refine ⟨hx, by omega, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (topFixes_ok (wide := wide) (sz := sz) (b := a + sz * (n + 1)) (by omega) (by omega) signed ws₂ di₂
    si₂ tok (by omega)) fun u₃ ⟨bu₃, mu₃, ku₃, pu₃⟩ => ?_
  have ws₃ := ws₂.of_keeps ku₃
  have di₃ : PtrAt u₃ W .edi 0 := by rw [PtrAt, ku₃.1 _ (by decide)]; exact di₂
  have si₃ : PtrAt u₃ W .esi (a + sz * (n + 1) + sz) := by rw [PtrAt, ku₃.1 _ (by decide)]; exact si₂
  rw [show ∀ (x y z w : List Instr), x ++ (y ++ (z ++ w)) = (x ++ y ++ z) ++ w by intros; simp, WP.block_append_iff]
  refine WP.mono (lastWord_ok (o := o) (y := a + o + sz * (n + 1)) ws₃ di₃ si₃ (by unfold neg; omega)
    (by unfold neg; omega) (by omega) (by omega) (fun h => by have := R.hP h; omega)) fun v ⟨mv, kv⟩ => k v ?_
  -- The values.
  have tF : topF u₂.mem W (a + sz * (n + 1)) signed = topF s₀.mem W (a + sz * (n + 1)) signed := by
    refine topF_congr fun t ht => ?_
    obtain ⟨hc, -, -, -, hw, -⟩ := R.terms t (hsg t ht)
    exact ⟨R.hdr I₂.frame hc fun h => (hw h).1, R.input I₂.frame (hsg t ht) (by omega) (by omega)⟩
  have hprev : prevAt wide W u₃ = prevAt wide W u₂ := by
    cases wide with
    | false => simp only [prevAt, Bool.false_eq_true, ↓reduceIte]; rw [pu₃ rfl]
    | true => simp only [prevAt, ↓reduceIte]; rw [mu₃]
  have eb := ebx_of_acc I₂.acc
  generalize hA : rowA s₀.mem W (a + sz) sz ts (n + 1) = A at eb
  have iprev := I₂.prev; have iout := I₂.out
  rw [hA] at iprev iout
  generalize hF : topF s₀.mem W (a + sz * (n + 1)) signed = F at tF
  rw [tF] at bu₃
  refine ⟨I₂.keep.trans ((ku₃.mono (by decide)).trans (kv.mono (by decide))), ?_, ?_⟩
  · rw [mv, mu₃]; exact I₂.frame.out (writeW32_outside _ _ _ (by omega))
  · rw [show n + 2 = n + 1 + 1 from rfl, sv]
    rw [mv, mu₃, sv_congr fun w hw => w32_write_ne (size := bytes) nw (by omega)
        (by have := mul_step (sz := sz) hw; omega) (.inl (by have := mul_step (sz := sz) hw; omega)) _,
      w32_write_self, iout, hprev, iprev, rowT, hA, hF,
      show A - 2 ^ (32 * (n + 1)) * F = A + 2 ^ (32 * (n + 1)) * (-F) by ring, outOf_next, BitVec.toNat_ofNat]
    congr 2
    have h32 := two_pow_pos' 32
    have e2 : ((u₃.gpr .ebx).toNat : Int) = (A / 2 ^ (32 * (n + 1)) + -F) % 2 ^ 32 := by
      rw [bu₃, eb, Int.sub_eq_add_neg, Int.emod_add_emod]
    have e3 := Int.emod_nonneg (A / 2 ^ (32 * (n + 1)) + -F) h32.ne'
    have : (u₃.gpr .ebx).toNat = ((A / 2 ^ (32 * (n + 1)) + -F) % 2 ^ 32).toNat := by omega
    rw [this]

end VG.Proof.Rsa.X86.InvBatchRt.F

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.R2Words VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx kw_eq)

/-! ## Arithmetic -/

theorem sv_cons (m : Mem) (W : Addr) (b sz : Nat) :
    ∀ N, sv m W b sz (N + 1) = VG.Proof.Mont.w32 m W b + 2 ^ 32 * sv m W (b + sz) sz N
  | 0 => by simp [sv]
  | N + 1 => by
    rw [sv, sv_cons m W b sz N, sv, show b + sz * (N + 1) = b + sz + sz * N by rw [Nat.mul_succ]; omega,
      show 32 * (N + 1) = 32 + 32 * N by omega, Nat.pow_add]
    ring

/-- The outputs from element 0: the row's value over `2^30`. -/
theorem outOf_div (T : Int) (N : Nat) : outOf T (N + 1) / 2 ^ 32 = ((T / 2 ^ 30) % 2 ^ (32 * N)).toNat := by
  have hk := two_pow_pos' 30
  unfold outOf lw
  rw [show 32 * (N + 1) = 32 + 32 * N by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    show (2 : Nat) ^ 32 = 4 * 2 ^ 30 by norm_num, Nat.mul_div_mul_left _ _ (by decide)]
  -- In `Int`.
  have e : (2 : Int) ^ (32 + 32 * N) = 2 ^ 30 * 2 ^ (2 + 32 * N) := by rw [← Int.pow_add]; congr 1; omega
  have hr := Int.emod_nonneg T (two_pow_pos' (32 + 32 * N)).ne'
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.natCast_ediv, Int.toNat_of_nonneg hr,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (two_pow_pos' (32 * N)).ne')]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [e, int_emod_mul _ _ _ hk, Int.add_mul_ediv_left _ _ hk.ne',
    Int.ediv_eq_zero_of_lt (Int.emod_nonneg _ hk.ne') (Int.emod_lt_of_pos _ hk), Int.zero_add,
    Int.emod_emod_of_dvd _ (pow_dvd_pow 2 (by omega))]

/-! ## The header's two scratch words -/

/-- `m'` agrees with `m` but on `sP` and `sE`. -/
def HdrFrame (W : Addr) (m m' : Mem) : Prop := ∀ x, (ofs W x < sP ∨ sP + 8 ≤ ofs W x) → m' x = m x

theorem HdrFrame.w32 {W : Addr} {m m' : Mem} (h : HdrFrame W m m') {d : Nat} (hd : d + 4 ≤ sP ∨ sP + 8 ≤ d)
    (hd' : d + 4 ≤ 2 ^ 64) : VG.Proof.Mont.w32 m' W d = VG.Proof.Mont.w32 m W d := by
  unfold VG.Proof.Mont.w32
  congr 1
  refine (Mem.readW_congr fun i hi => ?_).symm
  have hi' : i < 4 := by simpa using hi
  have e := ofs_off W (d := d) (i := i) (by omega)
  exact (h _ (by rw [e]; omega)).symm

theorem HdrFrame.readW {W : Addr} {m m' : Mem} (h : HdrFrame W m m') {d : Nat} (hd : d + 4 ≤ sP ∨ sP + 8 ≤ d)
    (hd' : d + 4 ≤ 2 ^ 64) : m'.readW (off W d) 32 = m.readW (off W d) 32 :=
  BitVec.eq_of_toNat_eq (h.w32 hd hd')

theorem sv_hdr {W : Addr} {m m' : Mem} (h : HdrFrame W m m') {b sz : Nat} (hb : sP + 8 ≤ b) (hbz : b + 2 ^ 32 + 4 ≤ 2 ^ 64) :
    ∀ {N}, sz * N ≤ 2 ^ 32 → sv m' W b sz N = sv m W b sz N
  | 0, _ => rfl
  | N + 1, hN => by
    have := Nat.mul_le_mul_left sz (show N ≤ N + 1 by omega)
    simp only [sv]
    rw [sv_hdr h hb hbz (by omega), h.w32 (.inr (by omega)) (by rw [Nat.mul_succ] at hN; omega)]

/-- The row's value is the same where only the scratch words changed. -/
theorem rowT_hdr {W : Addr} {m m' : Mem} (h : HdrFrame W m m') {a sz n : Nat} {ts signed : List Term}
    (hsg : ∀ t ∈ signed, t ∈ ts) (ha : sP + 8 ≤ a) (hfit : W.toNat + a + sz * (n + 2) ≤ 2 ^ 32)
    (hc : ∀ t ∈ ts, (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ t.c + 4 ≤ 2 ^ 32 ∧ t.x + 4 ≤ sz) :
    rowT m' W a sz n ts signed = rowT m W a sz n ts signed := by
  have m2 := mul_step (sz := sz) (show n + 1 < n + 2 by omega)
  have hW := W.isLt
  unfold rowT
  congr 1
  · unfold rowA
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨h1, h2, h3⟩ := hc t ht
    rw [h.readW h1 (by omega), sv_hdr h (by omega) (by omega) (by omega)]
  · congr 1
    unfold topF
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨h1, h2, h3⟩ := hc t (hsg t ht)
    rw [h.readW h1 (by omega), h.w32 (.inr (by omega)) (by omega)]

theorem HdrFrame.trans {W : Addr} {m₁ m₂ m₃ : Mem} (h₁ : HdrFrame W m₁ m₂) (h₂ : HdrFrame W m₂ m₃) :
    HdrFrame W m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem HdrFrame.write {W : Addr} {m : Mem} {d : Nat} (hd : sP ≤ d ∧ d + 4 ≤ sP + 8) (v : BitVec 32) :
    HdrFrame W m (m.writeW (off W d) v) := fun x hx =>
  writeW32_outside m W v (d := d) (by unfold sP at *; omega) x (by omega)

/-! ## The row's start -/

theorem setupN {W : Addr} {m : Mem} {V X : BitVec 32} {P : Prop} (hV : V = X) :
    HdrFrame W m (m.writeW (off W sE) V) ∧ (m.writeW (off W sE) V).readW (off W sE) 32 = X ∧ (False → P) :=
  ⟨HdrFrame.write (by decide) V, by rw [Mem.readW_writeW_self32, hV], False.elim⟩

theorem setupW {W : Addr} {m : Mem} {V X : BitVec 32} (hW : W.toNat + 184 ≤ 2 ^ 32) (hV : V = X) :
    HdrFrame W m ((m.writeW (off W sE) V).writeW (off W sP) (0 : BitVec 32)) ∧
      ((m.writeW (off W sE) V).writeW (off W sP) (0 : BitVec 32)).readW (off W sE) 32 = X ∧
      (True → VG.Proof.Mont.w32 ((m.writeW (off W sE) V).writeW (off W sP) (0 : BitVec 32)) W sP = 0) := by
  refine ⟨(HdrFrame.write (by decide) V).trans (HdrFrame.write (by decide) 0), ?_, fun _ => ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have := w32_write_ne (m := m.writeW (off W sE) V) (base := W) (size := 184) (o := sP) (d := sE) hW
      (by decide) (by decide) (.inr (by decide)) 0
    simp only [VG.Proof.Mont.w32] at this
    rw [this, Mem.readW_writeW_self32, hV]
  · rw [w32_write_self]; rfl

/-- After `ptr`: `sE` past the first `n` elements, the accumulator (and `sP`) zero. -/
theorem rowSetup_ok {u : State} {W : Addr} {bytes e n : Nat} (ws : Ws u W bytes) (di : PtrAt u W .edi 0)
    (si : PtrAt u W .esi e) (hh : u.mem.readW (off W halfSlot) 32 = BitVec.ofNat 32 (4 * n)) {sz : Nat}
    (hsz : sz = 16 ∨ sz = 20) (hb : sE + 4 ≤ bytes) (hhb : halfSlot + 4 ≤ bytes)
    (he : W.toNat + e + sz * n < 2 ^ 32) {wide : Bool} :
    WP isa (.block (([.mov .eax (.mem (sc halfSlot)), .mov .edx (.reg .eax)] : List Instr) ++
      (if sz = 16 then [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)]
       else [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .edx)]) ++
      ([.alu .add .eax (.reg .esi), .store (sc sE) .eax] : List Instr) ++
      ([.mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] : List Instr) ++
      (if wide then [.store (sc sP) .ebx] else []))) u fun v =>
      v.gpr .ebx = 0 ∧ v.gpr .ecx = 0 ∧ v.gpr .ebp = 0 ∧ HdrFrame W u.mem v.mem ∧
      v.mem.readW (off W sE) 32 = BitVec.ofNat 32 (W.toNat + (e + sz * n)) ∧
      (wide = true → VG.Proof.Mont.w32 v.mem W sP = 0) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] u v := by
  have nw := ws.nowrap
  have hsi := ptr_eq si
  obtain ⟨hdi, aH, rH⟩ := ptrRead ws di (d := halfSlot) (by omega)
  obtain ⟨-, aE, -⟩ := ptrRead ws di (d := sE) (by omega)
  obtain ⟨-, aP, -⟩ := ptrRead ws di (d := sP) (by unfold sP sE at *; omega)
  simp only [Nat.zero_add] at aH rH aE aP
  have wE := ws_write ws hb
  have wP := ws_write ws (y := sP) (n := 4) (by unfold sP sE at *; omega)
  have eE : sE = 180 := rfl
  have eP : sP = 176 := rfl
  rcases hsz with rfl | rfl <;> cases wide
  all_goals
    refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .ebp] (Q := fun v =>
      v.gpr .ebx = 0 ∧ v.gpr .ecx = 0 ∧ v.gpr .ebp = 0 ∧ HdrFrame W u.mem v.mem ∧
      v.mem.readW (off W sE) 32 = BitVec.ofNat 32 (W.toNat + (e + _ * n)) ∧
      (_ = true → VG.Proof.Mont.w32 v.mem W sP = 0)) ?_ rfl) fun v ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2, k⟩
    xrun [sc, hsi, hdi, aH, rH, hh, aE, aP, wE, wP, List.cons_append, List.nil_append, List.append_nil,
      Bool.false_eq_true, ↓reduceIte]
    first
    | exact setupN (BitVec.eq_of_toNat_eq (by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    | exact setupW (by unfold sP sE at *; omega) (BitVec.eq_of_toNat_eq (by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-! ## A row -/

variable {L : Lay} {B : Addr} {Z len N n : Nat}

/-- What a row's terms need, before the row. -/
def TermsOk (m : Mem) (B : Addr) (A0 sz o : Nat) (ts : List Term) : Prop :=
  ∀ t ∈ ts, t.c + 4 ≤ A0 ∧ t.m + 4 ≤ A0 ∧ t.x + 4 ≤ sz ∧ (t.x + 4 ≤ o ∨ o + 4 ≤ t.x) ∧
    (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m) ∧
    m.readW (off B t.m) 32 = maskW (m.readW (off B t.c) 32)

/-- A row writes its `n + 2` outputs (from the scratch element) and the header's scratch words. -/
def RowWr (B : Addr) (A0 sz o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ j < n + 2, ofs B x < A0 + o + sz * j ∨ A0 + o + sz * j + 4 ≤ ofs B x) →
    (ofs B x < sP ∨ sP + 8 ≤ ofs B x) → m' x = m x

theorem row_ok {s : State} (h : Bx L s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    {arr sz o : Nat} {ts signed : List Term} {wide : Bool} (hsz : sz = 16 ∨ sz = 20) (ho : o + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (harr : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hts : TermsOk s.mem B (rv (kw len) { arr := arr } n) sz o ts) (hsg : ∀ t ∈ signed, t ∈ ts)
    (bound : cB s.mem B ts * 2 ^ 32 ≤ if wide then 2 ^ 94 else 2 ^ 62) :
    WP isa (row L wide arr sz o ts signed) s fun t =>
      Bx L t B Z len N n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      RowWr B (rv (kw len) { arr := arr } n) sz o (n) s.mem t.mem ∧
      sv t.mem B (rv (kw len) { arr := arr } n + o + sz) sz (n + 1) =
        ((rowT s.mem B (rv (kw len) { arr := arr } n) sz (n) ts signed / 2 ^ 30) % 2 ^ (32 * (n + 1))).toNat := by
  have hn := h.nowrap
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have hZ := h.halfZ
  have eE : sE = 180 := rfl; have eP : sP = 176 := rfl; have eH : halfSlot = 96 := rfl
  generalize hA : rv (kw len) { arr := arr } n = A0 at *
  have hA' : rv (kw len) { arr := arr, byte := sz } n = A0 + sz := by
    rw [← hA]; simp only [rv]; omega
  have scr := h.ws.ws.workspace
  have ws : Ws s B Z := ⟨scr.wr, scr.nowrap⟩
  have di : PtrAt s B .edi 0 := by rw [PtrAt, RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega
  unfold row
  simp only [rowStart, List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (r := .esi) (t := .edx) (x := { arr := arr, byte := sz }) (by decide)
    (by decide) (by decide) (by decide) (by intro e; cases e) (by rw [hA']; have := mul_step (sz := sz) (show 0 < n + 2 by omega); omega) fun u K₁ m₁ p₁ => ?_)
  have mfit := mul_step (sz := sz) (show n < n + 2 by omega)
  rw [hA'] at p₁
  have wsu := ws.of_keeps K₁
  have diu : PtrAt u B .edi 0 := by rw [PtrAt, K₁.1 _ (by decide)]; exact di
  have hh : u.mem.readW (off B halfSlot) 32 = BitVec.ofNat 32 (4 * n) := by
    rw [m₁, h.slots.halfW]
  simp only [← List.append_assoc]
  refine WP.mono (rowSetup_ok (wide := wide) wsu diu p₁ hh hsz (by omega) (by omega)
    (by omega)) fun s₀ ⟨b₀, c₀, p₀, F₀, E₀, P₀, K₀⟩ => ?_
  rw [m₁] at F₀
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₀ := (K₁.mono (by decide)).trans (K₀.mono (by decide))
  have si₀ : PtrAt s₀ B .esi (A0 + sz) := by rw [PtrAt, K₀.1 _ (by decide)]; exact p₁
  -- The row's requirements at its start.
  have hdr : ∀ d, (d + 4 ≤ sP ∨ sP + 8 ≤ d) → d + 4 ≤ Z → s₀.mem.readW (off B d) 32 = s.mem.readW (off B d) 32 :=
    fun d hd hdz => F₀.readW hd (by omega)
  have R : RowOk s₀ B Z A0 sz o (n) ts wide := by
    refine ⟨ws.of_keeps K, by rw [PtrAt, K.1 _ (by decide)]; exact di, ho, hfit, fun _ => by omega,
      fun t ht => ?_, ?_⟩
    · obtain ⟨hc, hm, hx, hxo, hcp, hmp, hmask⟩ := hts t ht
      refine ⟨hc, hm, hx, hxo, fun _ => ⟨by omega, by omega⟩, ?_⟩
      rw [hdr _ hmp (by omega), hdr _ hcp (by omega), hmask]
    · have : cB s₀.mem B ts = cB s.mem B ts := by
        unfold cB; congr 1
        refine List.map_congr_left fun t ht => ?_
        obtain ⟨hc, -, -, -, hcp, -⟩ := hts t ht
        rw [hdr _ hcp (by omega)]
      rw [this]; exact bound
  have I₀ : RowInv s₀ B A0 sz o ts wide 0 s₀ := by
    refine ⟨Keeps.refl _ _, RowFrame.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · simp only [accOf, accM, acc96, acc64, rowA_zero, b₀, c₀, p₀]
      cases wide <;> simp
    · simp only [prevAt, prevOf_zero]
      cases wide
      · simp [p₀]
      · simpa using P₀ rfl
    · simp [sv, outOf_zero]
  refine WP.seq (WP.mono (rowLoop_ok R (by omega) he I₀ si₀ (by omega) (by rw [E₀]))
    fun v ⟨Iv, sv'⟩ => ?_)
  refine rowEnd_ok R Iv sv' hsg fun w D => ?_
  -- `edi` again, and the result.
  have hfr : ∀ x, (∀ j < n + 2, ofs B x < A0 + o + sz * j ∨ A0 + o + sz * j + 4 ≤ ofs B x) →
      (ofs B x < sP ∨ sP + 8 ≤ ofs B x) → w.mem x = s.mem x := fun x h1 h2 =>
    (D.frame x h1 fun _ => by omega).trans (F₀ x h2)
  have O0 : Outside B 0 Z s.mem w.mem := fun x hx => hfr x (fun j hj => by
    have := mul_step (sz := sz) (show j < n + 2 by omega); omega) (by omega)
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w := K.trans D.keep
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((KK.mono (by decide)).trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  have O160 : Outside B 160 (Z - 160) s.mem t₁.mem := fun x hx => by
    rw [U.mem]; exact hfr x (fun j hj => by
      have := mul_step (sz := sz) (show j < n + 2 by omega); unfold sP at harr; omega)
      (by unfold sP at *; omega)
  refine ⟨h.keep K' (by decide) (by decide) O160 (Nat.le_refl _) (by omega), K', fun x h1 h2 => by
    rw [U.mem]; exact hfr x h1 h2, ?_⟩
  rw [U.mem]
  have dec := sv_cons w.mem B (A0 + o) sz (n + 1)
  rw [D.out] at dec
  have hlt := (w.mem.readW (off B (A0 + o)) 32).isLt
  have e1 : sv w.mem B (A0 + o + sz) sz (n + 1) = outOf (rowT s₀.mem B A0 sz (n) ts signed) (n + 2) / 2 ^ 32 := by
    rw [dec]; simp only [VG.Proof.Mont.w32]; omega
  rw [e1, outOf_div, rowT_hdr (m := s.mem) F₀ hsg (by omega) (by omega) fun t ht => by
    obtain ⟨hc, -, hx, -, hcp, -⟩ := hts t ht
    exact ⟨hcp, by omega, hx⟩]

end VG.Proof.Rsa.X86.InvBatchRt.F
