module

import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel

/-!
# The Miller–Rabin round on PPC64LE: the context

`MCtx`: `Env` with `-c⁻¹ mod 2³²` in `r12`, for the Montgomery
multiplications (`mont_ok`). `Consts`: what the round reads and never
writes: the candidate `c` (array 0), `R mod c` (array 9), `c − R mod c`
(array 10), the exponent `E` (array 27) and the word after it. The round
writes only arrays 2, 3, 5, 6 and the table (`Mut`, `roundRanges`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (mrE mrA)

/-- The value of array `j`: its `2 w` digits. -/
abbrev arr (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (slot w j) (2 * w)

/-- `Env`, with `-c⁻¹ mod 2³²` in `r12`. -/
structure MCtx (s : State) (B : Addr) (Z w : Nat) : Prop extends Env s B Z w where
  h12 : (s.gpr .r12).toNat < 2 ^ 32
  inv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0

/-- The registers `MCtx` reads. -/
def mctxRegs : List Reg := [.r10, .r11, .r12, .r29, .r31]

/-! ## What the round may change -/

/-- The ranges of the arrays the round writes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2)), (slot w 6, 8 * (w + 2)),
    (slot w 11, 16 * (8 * (w + 2)))]

/-- Memory that changes only in the arrays the round writes. -/
abbrev Mut (B : Addr) (w : Nat) (m m' : Mem) : Prop := Outs B (roundRanges w) m m'

theorem Outs.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs B rs' m m' :=
  fun x hx => h x fun r hmem => by
    obtain ⟨r', h', h1, h2⟩ := hr r hmem
    have := hx r' h'
    omega

theorem Mut.of_outside {B : Addr} {w o : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * (w + 2)) m m')
    (ho : o = 2 ∨ o = 3 ∨ o = 5 ∨ o = 6) : Mut B w m m' :=
  Outs.of_outside h (by rcases ho with rfl | rfl | rfl | rfl <;> simp [roundRanges])

/-- An entry of the table. -/
theorem Mut.of_entry {B : Addr} {w j : Nat} {m m' : Mem} (h : Outside B (slot w (11 + j)) (8 * (w + 2)) m m')
    (hj : j < 16) : Mut B w m m' :=
  Outs.widen (Outs.of_outside h (List.mem_singleton_self _)) fun r hr => by
    rw [List.mem_singleton] at hr
    subst hr
    refine ⟨(slot w 11, 16 * (8 * (w + 2))), by simp [roundRanges], ?_, ?_⟩ <;>
      simp only [slot] <;> rw [Nat.add_mul] <;>
      have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 16 by omega) <;> rw [Nat.add_mul] at this <;>
      omega

/-- What a Montgomery multiplication into array `o` writes. -/
def montRanges (w o : Nat) : List (Nat × Nat) :=
  [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))]

theorem Mut.of_mont {B : Addr} {w o : Nat} {m m' : Mem} (h : Outs B (montRanges w o) m m')
    (ho : o = 5 ∨ o = 6) : Mut B w m m' :=
  Outs.widen h fun r hr => ⟨r, by
    simp only [montRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp [roundRanges], by omega, by omega⟩

/-- An array apart from the ranges that changed keeps its value. -/
theorem Outs.arrEq {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {j : Nat}
    (hj : j < 28) (hd : ∀ r ∈ rs, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (hn : slot w 28 ≤ 2 ^ 64) : arr m' B w j = arr m B w j :=
  h.val32 (fun r hr => by have := hd r hr; omega) (by have := slot_lt (w := w) hj; omega)

/-- An array apart from those of a Montgomery multiplication keeps its value. -/
theorem Outs.arrEq_mont {B : Addr} {w o : Nat} {m m' : Mem} (h : Outs B (montRanges w o) m m') {j : Nat}
    (hj : j < 28) (h2 : j ≠ 2) (h3 : j ≠ 3) (ho : j ≠ o) (hn : slot w 28 ≤ 2 ^ 64) :
    arr m' B w j = arr m B w j :=
  Outs.arrEq h hj (fun r hr => by
    simp only [montRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sep h2
    · exact slot_sep h3
    · exact slot_sep ho) hn

/-- An array apart from one that changed keeps its value. -/
theorem Outside.arrEq {B : Addr} {w o : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * (w + 2)) m m') {j : Nat}
    (hj : j < 28) (ho : j ≠ o) (hn : slot w 28 ≤ 2 ^ 64) : arr m' B w j = arr m B w j :=
  Outs.arrEq (Outs.of_outside h (List.mem_singleton_self _)) hj (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact slot_sep ho) hn

/-- The low digit of the candidate, apart from an array that changed. -/
theorem Outside.w32_0 {B : Addr} {w o : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * (w + 2)) m m')
    (ho : o ≠ 0) (hn : slot w 28 ≤ 2 ^ 64) : w32 m' B (slot w 0) = w32 m B (slot w 0) := by
  have := slot_sep (w := w) ho
  have := slot_lt (w := w) (show 0 < 28 by decide)
  exact h.w32 (by omega) (by omega)

/-- The low digit of the candidate, below every range that changed. -/
theorem Outs.w32_0 {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hd : ∀ r ∈ rs, slot w 0 + 8 * (w + 2) ≤ r.1) (hn : slot w 28 ≤ 2 ^ 64) :
    w32 m' B (slot w 0) = w32 m B (slot w 0) := by
  have := slot_lt (w := w) (show 0 < 28 by decide)
  exact congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off B (by omega)]; omega)

/-- An array the round does not write keeps its value. -/
theorem Mut.arr {B : Addr} {w : Nat} {m m' : Mem} (h : Mut B w m m') {j : Nat}
    (hj : j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 27)
    (hn : slot w 28 ≤ 2 ^ 64) : arr m' B w j = arr m B w j := by
  refine h.val32 (fun r hr => ?_) (by
    have := slot_lt (w := w) (show j < 28 by omega); omega)
  simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot] <;> omega

/-! ## The constants -/

/-- What the round reads and never writes. -/
structure Consts (m : Mem) (B : Addr) (w c : Nat) : Prop where
  cand : arr m B w 0 = c
  one : arr m B w aOne = 2 ^ (64 * w) % c
  minus : arr m B w aMinus = c - 2 ^ (64 * w) % c
  e : arr m B w aE = mrE c
  l : (m.readW (off B (slot w aE + 8 * w)) 64) = BitVec.twoPow 64 (mrA c % 64)

theorem Consts.of_mut {m m' : Mem} {B : Addr} {w c : Nat} (h : Consts m B w c) (hm : Mut B w m m')
    (hn : slot w 28 ≤ 2 ^ 64) : Consts m' B w c := by
  refine ⟨by rw [hm.arr (by simp) hn]; exact h.cand, by rw [hm.arr (by simp [aOne]) hn]; exact h.one,
    by rw [hm.arr (by simp [aMinus]) hn]; exact h.minus, by rw [hm.arr (by simp [aE]) hn]; exact h.e, ?_⟩
  rw [← h.l]
  refine Mem.readW_congr fun i hi => hm _ fun r hr => ?_
  have h27 := slot_lt (w := w) (show aE < 28 by decide)
  rw [ofs_off B (by simp only [aE] at h27 ⊢; omega)]
  simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, aE] <;> omega

/-! ## Montgomery multiplications -/

theorem MCtx.keep {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : MCtx s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ mctxRegs, r ∉ rs) (hm : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) : MCtx t B Z w :=
  { h.toEnv.keep k fun r hr' => hr r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> decide) with
    h12 := by rw [k.gpr _ (hr _ (by decide))]; exact h.h12
    inv := by rw [k.gpr _ (hr _ (by decide)), hm]; exact h.inv }

/-- `montOp o a b`, for arrays among 5 and 6, `[b] < c`. -/
theorem mont_ok {s : State} {B : Addr} {Z w : Nat} (h : MCtx s B Z w) {o a b : Nat}
    (ho : o = 5 ∨ o = 6) (ha : a = 5 ∨ a = 6) (hb : b = 5 ∨ b = 6) (hB : arr s.mem B w b < arr s.mem B w 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < arr s.mem B w 0 ∧
        arr t.mem B w o * 2 ^ (64 * w) % arr s.mem B w 0 = arr s.mem B w a * arr s.mem B w b % arr s.mem B w 0 ∧
        Outs B (montRanges w o) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep Pub.montRegs s t := by
  have hw := h.hw
  have hw' := h.hw'
  have h8 := slot_lt (w := w) (show 8 < 28 by decide)
  have hZ := h.hZ
  refine WP.mono (Pub.montOp_ok h.hs (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  rw [ofs_off B (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega

end VG.Proof.MillerRabin.PPC64LE
