module

public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# x86 (32-bit): straight-line SSE2 code, by evaluation

As `Straight`, for the 128-bit registers of SSE2 code: a block of moves,
bitwise operations, shifts, shuffles and unpacks of XMM registers, and of
`movdqu` loads and stores on three memory areas, is evaluated over an
abstract domain (`XDom`) by `eval`: 16-byte *slots* `[base + 16k]`, read and
written, read-only *external* quadruple words `[ext + 16k]`, and a static
table of constants (`movdquTbl`). `run` says that the machine then runs the
block without faulting, and that its registers and slots are related to the
abstract result as they were to the abstract initial values.

An `XDom` has every instruction's operation (`Un`, `XBinOp`) on abstract
128-bit values. `ofDom` makes one of a domain of `Bitslice` on 128-bit
words: the operations that move bits (`unMoves`, `binMoves`) are XORs of
rotations masked by constants, those the code here uses. So the truth-table
domain checks circuits, and the lane domain checks linear layers that cross
the lanes (`linear_ok`).
-/

@[expose] public section

namespace VG.X86.StraightSse

open VG.Bitslice
open VG.X86.Straight (toNat_setWidth32)

/-! ## The operations that move bits -/

/-- An operation on one XMM register. -/
inductive Un
  | shift (op : XShiftOp) (n : BitVec 8)
  | pshufd (o : BitVec 8)
  | pshuflw (o : BitVec 8)
  | pshufhw (o : BitVec 8)
  deriving DecidableEq, Repr

def Un.eval : Un → BitVec 128 → BitVec 128
  | .shift op n, x => op.eval x n
  | .pshufd o, x => shufDwords x o
  | .pshuflw o, x => shufLowWords x o
  | .pshufhw o, x => shufHighWords x o

/-- The bit of the operand that bit `p` of the result is, if any. -/
def Un.src : Un → Nat → Option Nat
  | .shift .psrlq n, p => if p % 64 + n.toNat < 64 then some (p + n.toNat) else none
  | .shift .psllq n, p => if n.toNat ≤ p % 64 then some (p - n.toNat) else none
  | .shift .psrld n, p => if p % 32 + n.toNat < 32 then some (p + n.toNat) else none
  | .shift .pslld n, p => if n.toNat ≤ p % 32 then some (p - n.toNat) else none
  | .shift .psrldq n, p => if p + 8 * n.toNat < 128 then some (p + 8 * n.toNat) else none
  | .shift .pslldq n, p => if 8 * n.toNat ≤ p then some (p - 8 * n.toNat) else none
  | .shift .psraw n, p => some (16 * (p / 16) + min 15 (p % 16 + n.toNat))
  | .pshufd o, p => some (32 * (o.extractLsb' (2 * (p / 32)) 2).toNat + p % 32)
  | .pshuflw o, p => some (if p < 64 then 16 * (o.extractLsb' (2 * (p / 16)) 2).toNat + p % 16 else p)
  | .pshufhw o, p =>
    some (if p < 64 then p else 16 * (4 + (o.extractLsb' (2 * (p / 16 - 4)) 2).toNat) + p % 16)

/-- The bit of the operands (the first, or the second) that bit `p` of the
result of an unpacking is. -/
def binSrc : XBinOp → Nat → Option (Bool × Nat)
  | .punpcklwd, p => some (decide (p / 16 % 2 = 1), 16 * (p / 32) + p % 16)
  | .punpckhwd, p => some (decide (p / 16 % 2 = 1), 64 + 16 * (p / 32) + p % 16)
  | .punpckldq, p => some (decide (p / 32 % 2 = 1), 32 * (p / 64) + p % 32)
  | .punpckhdq, p => some (decide (p / 32 % 2 = 1), 64 + 32 * (p / 64) + p % 32)
  | .punpcklqdq, p => some (if p < 64 then (false, p) else (true, p - 64))
  | .punpckhqdq, p => some (if p < 64 then (false, 64 + p) else (true, p))
  | _, _ => none

/-- Bit `q` of `x`, if any. -/
def bitOpt (x : BitVec 128) : Option Nat → Bool
  | some q => x.getLsbD q
  | none => false

theorem getLsbD_qword (x : BitVec 128) {q i : Nat} (hi : i < 64) :
    (qword x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qword, hi]

/-- `XOR` of `x` rotated right by `r` and masked by `m`, for `(r, m)` in `l`. -/
def movesC (l : List (Nat × BitVec 128)) (x : BitVec 128) : BitVec 128 :=
  l.foldr (fun m acc => (x.rotateRight m.1 &&& m.2) ^^^ acc) 0

/-- The bits of the operand that `movesC l` XORs into bit `p`. -/
def movesSrc (l : List (Nat × BitVec 128)) (p : Nat) : List Nat :=
  l.filterMap fun m => if m.2.getLsbD p then some ((p + m.1) % 128) else none

theorem movesC_bit (l : List (Nat × BitVec 128)) (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (movesC l x).getLsbD p = (movesSrc l p).foldr (fun q acc => x.getLsbD q ^^ acc) false := by
  induction l with
  | nil => simp [movesC, movesSrc]
  | cons m l ih =>
    have e : movesC (m :: l) x = (x.rotateRight m.1 &&& m.2) ^^^ movesC l x := rfl
    rw [e, BitVec.getLsbD_xor, BitVec.getLsbD_and, getLsbD_rotateRight_lt x m.1 p hp, ih]
    unfold movesSrc
    rw [List.filterMap_cons]
    cases m.2.getLsbD p <;> simp

/-- `l` moves the bits as `g` says. -/
def realizes (l : List (Nat × BitVec 128)) (g : Nat → Option Nat) : Bool :=
  (List.range 128).all fun p => movesSrc l p == (g p).toList

theorem movesC_eq {l : List (Nat × BitVec 128)} {g : Nat → Option Nat} (h : realizes l g = true)
    (x : BitVec 128) {p : Nat} (hp : p < 128) : (movesC l x).getLsbD p = bitOpt x (g p) := by
  have := List.all_eq_true.mp h p (List.mem_range.mpr hp)
  rw [movesC_bit l x hp, eq_of_beq this]
  cases g p <;> simp [bitOpt]

/-- The moves of the operations on one register. -/
def unMoves : Un → Option (List (Nat × BitVec 128))
  | .shift .psrlq 1 => some [(1, 0x7fffffffffffffff7fffffffffffffff)]
  | .shift .psrlq 2 => some [(2, 0x3fffffffffffffff3fffffffffffffff)]
  | .shift .psrlq 4 => some [(4, 0xfffffffffffffff0fffffffffffffff)]
  | .shift .psllq 1 => some [(127, 0xfffffffffffffffefffffffffffffffe)]
  | .shift .psllq 2 => some [(126, 0xfffffffffffffffcfffffffffffffffc)]
  | .shift .psllq 4 => some [(124, 0xfffffffffffffff0fffffffffffffff0)]
  | .shift .pslld 1 => some [(127, 0xfffffffefffffffefffffffefffffffe)]
  | .shift .pslld 4 => some [(124, 0xfffffff0fffffff0fffffff0fffffff0)]
  | .shift .pslld 8 => some [(120, 0xffffff00ffffff00ffffff00ffffff00)]
  | .shift .pslld 9 => some [(119, 0xfffffe00fffffe00fffffe00fffffe00)]
  | .shift .pslld 10 => some [(118, 0xfffffc00fffffc00fffffc00fffffc00)]
  | .shift .pslld 11 => some [(117, 0xfffff800fffff800fffff800fffff800)]
  | .shift .pslld 12 => some [(116, 0xfffff000fffff000fffff000fffff000)]
  | .shift .pslld 13 => some [(115, 0xffffe000ffffe000ffffe000ffffe000)]
  | .shift .pslld 14 => some [(114, 0xffffc000ffffc000ffffc000ffffc000)]
  | .shift .pslld 15 => some [(113, 0xffff8000ffff8000ffff8000ffff8000)]
  | .shift .pslld 24 => some [(104, 0xff000000ff000000ff000000ff000000)]
  | .shift .psrld 4 => some [(4, 0xfffffff0fffffff0fffffff0fffffff)]
  | .shift .psrld 8 => some [(8, 0xffffff00ffffff00ffffff00ffffff)]
  | .shift .psraw 15 => some [(0, 0x80008000800080008000800080008000), (1,
      0x40004000400040004000400040004000), (2, 0x20002000200020002000200020002000), (3,
      0x10001000100010001000100010001000), (4, 0x8000800080008000800080008000800), (5,
      0x4000400040004000400040004000400), (6, 0x2000200020002000200020002000200), (7,
      0x1000100010001000100010001000100), (8, 0x800080008000800080008000800080), (9,
      0x400040004000400040004000400040), (10, 0x200020002000200020002000200020), (11,
      0x100010001000100010001000100010), (12, 0x80008000800080008000800080008), (13,
      0x40004000400040004000400040004), (14, 0x20002000200020002000200020002), (15,
      0x10001000100010001000100010001)]
  | .shift .pslldq 8 => some [(64, 0xffffffffffffffff0000000000000000)]
  | .shift .psrldq 8 => some [(64, 0xffffffffffffffff)]
  | .pshufd 0xee => some [(0, 0xffffffffffffffff0000000000000000), (64, 0xffffffffffffffff)]
  | .pshufd 0x44 => some [(0, 0xffffffffffffffff), (64, 0xffffffffffffffff0000000000000000)]
  | .pshufd 0xb1 => some [(32, 0xffffffff00000000ffffffff), (96, 0xffffffff00000000ffffffff00000000)]
  | .pshufd 0xd8 => some [(0, 0xffffffff0000000000000000ffffffff), (32, 0xffffffff00000000), (96,
      0xffffffff0000000000000000)]
  | .pshuflw 0x39 => some [(0, 0xffffffffffffffff0000000000000000), (16, 0xffffffffffff), (80,
      0xffff000000000000)]
  | .pshuflw 0xb1 => some [(0, 0xffffffffffffffff0000000000000000), (16, 0xffff0000ffff), (112, 0xffff0000ffff0000)]
  | .pshuflw 0xd8 => some [(0, 0xffffffffffffffffffff00000000ffff), (16, 0xffff0000), (112, 0xffff00000000)]
  | .pshufhw 0xb1 => some [(0, 0xffffffffffffffff), (16, 0xffff0000ffff0000000000000000),
      (112, 0xffff0000ffff00000000000000000000)]
  | .pshufhw 0xd8 => some [(0, 0xffff00000000ffffffffffffffffffff), (16, 0xffff00000000000000000000),
      (112, 0xffff000000000000000000000000)]
  | .shift .psrlq 8 => some [(8, 0xffffffffffffff00ffffffffffffff)]
  | .shift .psrlq 24 => some [(24, 0xffffffffff000000ffffffffff)]
  | .shift .psllq 8 => some [(120, 0xffffffffffffff00ffffffffffffff00)]
  | .shift .psllq 24 => some [(104, 0xffffffffff000000ffffffffff000000)]
  | .shift .psrld 24 => some [(24, 0xff000000ff000000ff000000ff)]
  | .pshufd 0x39 => some [(32, 0xffffffffffffffffffffffffffffffff)]
  | .pshufd 0x4e => some [(64, 0xffffffffffffffffffffffffffffffff)]
  | .pshuflw 0xb4 => some [(0, 0xffffffffffffffff00000000ffffffff), (16, 0xffff00000000), (112, 0xffff000000000000)]
  | .pshufhw 0xb4 => some [(0, 0xffffffffffffffffffffffff), (16, 0xffff000000000000000000000000),
      (112, 0xffff0000000000000000000000000000)]
  | _ => none

/-- The moves of the unpackings, of each operand. -/
def binMoves : XBinOp → Option (List (Nat × BitVec 128) × List (Nat × BitVec 128))
  | .punpcklwd => some ([(0, 0xffff), (80, 0xffff000000000000000000000000), (96,
      0xffff0000000000000000), (112, 0xffff00000000)],
  [(64, 0xffff0000000000000000000000000000), (80, 0xffff00000000000000000000), (96,
      0xffff000000000000), (112, 0xffff0000)])
  | .punpckhwd => some ([(16, 0xffff000000000000000000000000), (32, 0xffff0000000000000000), (48,
      0xffff00000000), (64, 0xffff)],
  [(0, 0xffff0000000000000000000000000000), (16, 0xffff00000000000000000000), (32,
      0xffff000000000000), (48, 0xffff0000)])
  | .punpckldq => some ([(0, 0xffffffff), (96, 0xffffffff0000000000000000)],
      [(64, 0xffffffff000000000000000000000000), (96, 0xffffffff00000000)])
  | .punpckhdq => some ([(32, 0xffffffff0000000000000000), (64, 0xffffffff)],
      [(0, 0xffffffff000000000000000000000000), (32, 0xffffffff00000000)])
  | .punpcklqdq => some ([(0, 0xffffffffffffffff)],
      [(64, 0xffffffffffffffff0000000000000000)])
  | .punpckhqdq => some ([(64, 0xffffffffffffffff)],
      [(0, 0xffffffffffffffff0000000000000000)])
  | _ => none

/-! ## The bits of the operations -/

theorem bit_word (x : BitVec 128) (p : Nat) :
    x.getLsbD p = (word x (p / 16)).getLsbD (p % 16) := by
  rw [getLsbD_word _ _ _ (Nat.mod_lt _ (by omega_using []))]
  exact congrArg _ (by omega_using [])

theorem bit_dword (x : BitVec 128) (p : Nat) :
    x.getLsbD p = (dword x (p / 32)).getLsbD (p % 32) := by
  rw [getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
  exact congrArg _ (by omega_using [])

theorem bit_qwords (a b : BitVec 64) {p : Nat} (hp : p < 128) :
    (a ++ b).getLsbD p = if p < 64 then b.getLsbD (p % 64) else a.getLsbD (p % 64) := by
  rw [BitVec.getLsbD_append]
  by_cases h : p < 64
  · rw [ite_eq_left h, ite_eq_left h, Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h, ite_eq_right h]; exact congrArg _ (by omega_using [h, hp])

theorem bit_qword (x : BitVec 128) (q p : Nat) :
    (qword x q).getLsbD (p % 64) = x.getLsbD (64 * q + p % 64) :=
  getLsbD_qword x (Nat.mod_lt _ (by omega_using []))

/-- A whole-number shift inside the lane `[L * (p / L), …)`. -/
theorem shift_bit (op : XShiftOp) (n : BitVec 8) (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (XShiftOp.eval op x n).getLsbD p = bitOpt x ((Un.shift op n).src p) := by
  have h4 : p / 32 < 4 := by omega_using [hp]
  have hm : p % 32 < 32 := Nat.mod_lt _ (by omega_using [])
  have hq : p % 64 < 64 := Nat.mod_lt _ (by omega_using [])
  have hdw : ∀ a : BitVec 128, dword a (p / 32) = dword a (p / 32) := fun _ => rfl
  cases op
  case pslld =>
    simp only [Un.src]
    by_cases hn : n.toNat < 32
    · rw [bit_dword, dword_pslld x n hn h4, BitVec.getLsbD_shiftLeft, decide_eq_true hm, Bool.true_and]
      by_cases h : n.toNat ≤ p % 32
      · rw [ite_eq_left h, decide_eq_false (by omega_using [h]), Bool.not_false, Bool.true_and, bitOpt,
          getLsbD_dword, decide_eq_true (by omega_using [hm]), Bool.true_and]
        exact congrArg _ (by omega_using [h])
      · rw [ite_eq_right h, decide_eq_true (by omega_using [h])]; rfl
    · simp only [XShiftOp.eval, show 31 < n.toNat by omega_using [hn], ite_true]
      rw [ite_eq_right (by omega_using [hn, hm])]; simp [bitOpt]
  case psrld =>
    simp only [Un.src]
    by_cases hn : n.toNat < 32
    · rw [bit_dword, dword_psrld x n hn h4, BitVec.getLsbD_ushiftRight, getLsbD_dword]
      by_cases h : p % 32 + n.toNat < 32
      · rw [ite_eq_left h, decide_eq_true (by omega_using [h]), Bool.true_and, bitOpt]
        exact congrArg _ (by omega_using [h])
      · rw [ite_eq_right h, decide_eq_false (by omega_using [h])]; rfl
    · simp only [XShiftOp.eval, show 31 < n.toNat by omega_using [hn], ite_true]
      rw [ite_eq_right (by omega_using [hn])]; simp [bitOpt]
  case psllq =>
    simp only [Un.src, XShiftOp.eval]
    by_cases hn : n.toNat < 64
    · rw [ite_eq_right (show ¬ 63 < n.toNat by omega_using [hn]), bit_qwords _ _ hp]
      simp only [BitVec.getLsbD_shiftLeft, decide_eq_true hq, Bool.true_and]
      by_cases h : n.toNat ≤ p % 64
      · rw [ite_eq_left h, bitOpt]
        simp only [show ¬ p % 64 < n.toNat by omega_using [h], decide_false, Bool.not_false, Bool.true_and]
        rw [getLsbD_qword _ (by omega_using [hq]), getLsbD_qword _ (by omega_using [hq])]
        split <;> exact congrArg _ (by omega_using [h, hp, (by assumption)])
      · rw [ite_eq_right h]
        simp only [show p % 64 < n.toNat by omega_using [h], decide_true, Bool.not_true, Bool.false_and, ite_self]; rfl
    · rw [ite_eq_left (show 63 < n.toNat by omega_using [hn]), ite_eq_right (by omega_using [hn, hq])]
      simp [bitOpt]
  case psrlq =>
    simp only [Un.src, XShiftOp.eval]
    by_cases hn : n.toNat < 64
    · rw [ite_eq_right (show ¬ 63 < n.toNat by omega_using [hn]), bit_qwords _ _ hp]
      simp only [BitVec.getLsbD_ushiftRight, qword, BitVec.getLsbD_extractLsb']
      by_cases h : p % 64 + n.toNat < 64
      · rw [ite_eq_left h, bitOpt]
        simp only [show n.toNat + p % 64 < 64 by omega_using [h], decide_true, Bool.true_and]
        split <;> exact congrArg _ (by omega_using [h, hp, (by assumption)])
      · rw [ite_eq_right h]
        simp only [show ¬ n.toNat + p % 64 < 64 by omega_using [h], decide_false, Bool.false_and, ite_self]; rfl
    · rw [ite_eq_left (show 63 < n.toNat by omega_using [hn]), ite_eq_right (by omega_using [hn])]
      simp [bitOpt]
  case pslldq =>
    simp only [Un.src, XShiftOp.eval, BitVec.getLsbD_shiftLeft, decide_eq_true hp, Bool.true_and]
    by_cases h : 8 * n.toNat ≤ p
    · rw [ite_eq_left h, show min n.toNat 16 = n.toNat by omega_using [h, hp], bitOpt,
        decide_eq_false (by omega_using [h]), Bool.not_false, Bool.true_and]
      exact congrArg _ (by omega_using [])
    · rw [ite_eq_right h, decide_eq_true (by omega_using [h, hp])]; rfl
  case psrldq =>
    simp only [Un.src, XShiftOp.eval, BitVec.getLsbD_ushiftRight]
    by_cases h : p + 8 * n.toNat < 128
    · rw [ite_eq_left h, bitOpt]
      exact congrArg _ (by omega_using [h])
    · rw [ite_eq_right h, bitOpt]
      exact BitVec.getLsbD_of_ge _ _ (by omega_using [h])
  case psraw =>
    simp only [Un.src, XShiftOp.eval, bitOpt]
    rw [show p = 16 * (p / 16) + p % 16 by omega_using [],
      getLsbD_ofWords _ (by omega_using [hp]) (Nat.mod_lt _ (by omega_using []))]
    generalize p / 16 = a
    have hr : p % 16 < 16 := Nat.mod_lt _ (by omega_using [])
    generalize p % 16 = r at hr ⊢
    rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega_using [hr]), Bool.not_false, Bool.true_and,
      show (16 * a + r) / 16 = a by omega_using [hr], show (16 * a + r) % 16 = r by omega_using [hr]]
    by_cases h : min n.toNat 16 + r < 16
    · rw [ite_eq_left h, getLsbD_word _ _ _ h]; exact congrArg _ (by omega_using [h])
    · rw [ite_eq_right h, BitVec.msb_eq_getLsbD_last, getLsbD_word _ _ _ (by omega_using [])]
      exact congrArg _ (by omega_using [h, hr])

theorem un_bit (u : Un) (x : BitVec 128) {p : Nat} (hp : p < 128) :
    (u.eval x).getLsbD p = bitOpt x (u.src p) := by
  have hm : p % 32 < 32 := Nat.mod_lt _ (by omega_using [])
  have hw : p % 16 < 16 := Nat.mod_lt _ (by omega_using [])
  cases u with
  | shift op n => exact shift_bit op n x hp
  | pshufd o =>
    simp only [Un.eval, Un.src, bitOpt]
    rw [bit_dword, dword_shufDwords x o (by omega_using [hp]), getLsbD_dword, decide_eq_true hm, Bool.true_and]
  | pshuflw o =>
    simp only [Un.eval, Un.src, bitOpt, shufLowWords]
    rw [bit_word, word_ofWords _ (by omega_using [hp])]
    by_cases h : p < 64
    · rw [ite_eq_left h, ite_eq_left (by omega_using [h]), getLsbD_word _ _ _ hw]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h]), ← bit_word]
  | pshufhw o =>
    simp only [Un.eval, Un.src, bitOpt, shufHighWords]
    rw [bit_word, word_ofWords _ (by omega_using [hp])]
    by_cases h : p < 64
    · rw [ite_eq_left h, ite_eq_left (by omega_using [h]), ← bit_word]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h]), getLsbD_word _ _ _ hw]

theorem bin_bit {op : XBinOp} {s : Bool} {q p : Nat} (x y : BitVec 128) (hp : p < 128)
    (h : binSrc op p = some (s, q)) : (op.eval x y).getLsbD p = (if s then y else x).getLsbD q := by
  have hw : p % 16 < 16 := Nat.mod_lt _ (by omega_using [])
  cases op <;> simp only [binSrc, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  case punpcklwd =>
    obtain ⟨rfl, rfl⟩ := h
    rw [bit_word, word_punpcklwd _ _ (by omega_using [hp])]
    by_cases h : p / 16 % 2 = 1
    · rw [ite_eq_right (by omega_using [h]), getLsbD_word _ _ _ hw]
      simp only [h, decide_true, ite_true]; exact congrArg _ (by omega_using [])
    · rw [ite_eq_left (by omega_using [h]), getLsbD_word _ _ _ hw]
      simp only [h, decide_false, Bool.false_eq_true, ite_false]; exact congrArg _ (by omega_using [])
  case punpckhwd =>
    obtain ⟨rfl, rfl⟩ := h
    rw [bit_word, word_punpckhwd _ _ (by omega_using [hp])]
    by_cases h : p / 16 % 2 = 1
    · rw [ite_eq_right (by omega_using [h]), getLsbD_word _ _ _ hw]
      simp only [h, decide_true, ite_true]; exact congrArg _ (by omega_using [])
    · rw [ite_eq_left (by omega_using [h]), getLsbD_word _ _ _ hw]
      simp only [h, decide_false, Bool.false_eq_true, ite_false]; exact congrArg _ (by omega_using [])
  case punpckldq =>
    obtain ⟨rfl, rfl⟩ := h
    rw [punpckldq_eq, bit_dword]
    rcases cases4 (show p / 32 < 4 by omega_using [hp]) with e | e | e | e <;> rw [e]
    · rw [dword_ofDwords_0, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ite_false]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_1, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, decide_true, ite_true]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_2, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ite_false]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_3, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, decide_true, ite_true]
      exact congrArg _ (by omega_using [e])
  case punpckhdq =>
    obtain ⟨rfl, rfl⟩ := h
    rw [punpckhdq_eq, bit_dword]
    rcases cases4 (show p / 32 < 4 by omega_using [hp]) with e | e | e | e <;> rw [e]
    · rw [dword_ofDwords_0, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ite_false]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_1, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, decide_true, ite_true]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_2, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ite_false]
      exact congrArg _ (by omega_using [e])
    · rw [dword_ofDwords_3, getLsbD_dword, decide_eq_true (Nat.mod_lt _ (by omega_using [])), Bool.true_and]
      simp only [Nat.reduceMod, decide_true, ite_true]
      exact congrArg _ (by omega_using [e])
  case punpcklqdq =>
    simp only [XBinOp.eval]
    rw [bit_qwords _ _ hp, bit_qword, bit_qword]
    by_cases hh : p < 64
    · rw [ite_eq_left hh] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact congrArg _ (by omega_using [hh])
    · rw [ite_eq_right hh] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact congrArg _ (by omega_using [hh, hp])
  case punpckhqdq =>
    simp only [XBinOp.eval]
    rw [bit_qwords _ _ hp, bit_qword, bit_qword]
    by_cases hh : p < 64
    · rw [ite_eq_left hh] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact congrArg _ (by omega_using [hh])
    · rw [ite_eq_right hh] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact congrArg _ (by omega_using [hh, hp])

/-! ## The domains -/

/-- The abstract versions of the operations on XMM registers; `none` when the
domain cannot represent the result. -/
structure XDom (α : Type) where
  un : Un → α → Option α
  bin : XBinOp → α → α → Option α
  const : BitVec 128 → Option α

structure XDom.Sound {α : Type} (D : XDom α) (R : α → BitVec 128 → Prop) : Prop where
  un : ∀ {u : Un} {a c : α} {x : BitVec 128}, R a x → D.un u a = some c → R c (u.eval x)
  bin : ∀ {op : XBinOp} {a b c : α} {x y : BitVec 128}, R a x → R b y → D.bin op a b = some c → R c (op.eval x y)
  const : ∀ {v : BitVec 128} {c : α}, D.const v = some c → R c v

section ofDom
variable {α : Type} (D : Dom α 128)

/-- `movesC`, on abstract values. -/
def movesA (a : α) : List (Nat × BitVec 128) → Option α
  | [] => D.const 0
  | m :: l => (movesA a l).bind fun acc => (D.const m.2).bind fun k => (D.ror m.1 a).bind fun t =>
      (D.and t k).bind fun t' => D.xor t' acc

theorem movesA_sound {R : α → BitVec 128 → Prop} (hD : D.Sound R) {a : α} {x : BitVec 128} (ha : R a x) :
    ∀ {l : List (Nat × BitVec 128)} {c : α}, movesA D a l = some c → R c (movesC l x)
  | [], _, h => hD.const h
  | m :: l, c, h => by
    simp only [movesA, Option.bind_eq_some_iff] at h
    obtain ⟨acc, hacc, k, hk, t, ht, t', ht', hc⟩ := h
    exact hD.xor (hD.and (hD.ror ha ht) (hD.const hk) ht') (movesA_sound hD ha hacc) hc

/-- The domain of a domain of `Bitslice`. -/
def ofDom : XDom α where
  un u a := (unMoves u).bind (movesA D a)
  bin op a b := match op with
    | .movdqa => some b
    | .pxor => D.xor a b
    | .por => D.or a b
    | .pand => D.and a b
    | .pandn => (D.const (BitVec.allOnes 128)).bind fun o => (D.xor a o).bind fun n => D.and n b
    | op => (binMoves op).bind fun m => (movesA D a m.1).bind fun x => (movesA D b m.2).bind (D.xor x)
  const := D.const

theorem unMoves_ok : ∀ {u : Un} {l : List (Nat × BitVec 128)}, unMoves u = some l → realizes l u.src = true := by
  intro u l h
  unfold unMoves at h
  split at h <;> first | (cases h; done) | (cases h; kernel_rfl)

/-- The moves of an unpacking put together are what it does. -/
def realizes2 (l : List (Nat × BitVec 128) × List (Nat × BitVec 128)) (g : Nat → Option (Bool × Nat)) : Bool :=
  (List.range 128).all fun p => match g p with
    | some (false, q) => movesSrc l.1 p == [q] && movesSrc l.2 p == []
    | some (true, q) => movesSrc l.1 p == [] && movesSrc l.2 p == [q]
    | none => false

theorem binMoves_ok : ∀ {op : XBinOp} {l : List (Nat × BitVec 128) × List (Nat × BitVec 128)},
    binMoves op = some l → realizes2 l (binSrc op) = true := by
  intro op l h
  unfold binMoves at h
  split at h <;> first | (cases h; done) | (cases h; kernel_rfl)

theorem un_moves {u : Un} {l : List (Nat × BitVec 128)} (h : unMoves u = some l) (x : BitVec 128) :
    movesC l x = u.eval x :=
  BitVec.eq_of_getLsbD_eq fun p hp => by rw [movesC_eq (unMoves_ok h) x hp, un_bit u x hp]

theorem bin_moves {op : XBinOp} {l : List (Nat × BitVec 128) × List (Nat × BitVec 128)}
    (h : binMoves op = some l) (x y : BitVec 128) : movesC l.1 x ^^^ movesC l.2 y = op.eval x y :=
  BitVec.eq_of_getLsbD_eq fun p hp => by
    have := List.all_eq_true.mp (binMoves_ok h) p (List.mem_range.mpr hp)
    rw [BitVec.getLsbD_xor, movesC_bit _ _ hp, movesC_bit _ _ hp]
    split at this
    · rename_i q hg
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [this.1, this.2, bin_bit x y hp hg]; simp
    · rename_i q hg
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [this.1, this.2, bin_bit x y hp hg]; simp
    · cases this

theorem ofDom_sound {R : α → BitVec 128 → Prop} (hD : D.Sound R) : (ofDom D).Sound R where
  un {u a c x} ha h := by
    simp only [ofDom, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    rw [← un_moves hl]; exact movesA_sound D hD ha h
  bin {op a b c x y} ha hb h := by
    have hmv : ∀ {op : XBinOp}, (binMoves op).bind (fun m => (movesA D a m.1).bind fun x =>
        (movesA D b m.2).bind (D.xor x)) = some c → R c (op.eval x y) := by
      intro op h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, u, hu, v, hv, h⟩ := h
      rw [← bin_moves hl]
      exact hD.xor (movesA_sound D hD ha hu) (movesA_sound D hD hb hv) h
    cases op
    case movdqa => cases h; exact hb
    case pxor => exact hD.xor ha hb h
    case por => exact hD.or ha hb h
    case pand => exact hD.and ha hb h
    case pandn =>
      simp only [ofDom, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, n, hn, h⟩ := h
      have e : XBinOp.eval .pandn x y = (x ^^^ BitVec.allOnes 128) &&& y := by
        rw [BitVec.xor_allOnes]; rfl
      rw [e]
      exact hD.and (hD.xor ha (hD.const ho) hn) hb h
    all_goals exact hmv h
  const h := hD.const h

end ofDom

/-! ## The evaluator -/

/-- The memory areas: slots `[base + 16k]`, `k < slots`; external quadruple
words `[ext + 16k]`, `k < exts`; and the static `name`, at `tbl`. -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  tbl : Reg
  name : String
  words : List (BitVec 64)

structure Env (α : Type) where
  reg : XReg → Option α
  slot : Nat → Option α

variable {α : Type}

def Env.setReg (e : Env α) (d : XReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

def Cfg.loc (c : Cfg) (m : MemOp) : Option Where :=
  if m.disp % 16 = 0 then
    if m.base = c.base ∧ m.disp / 16 < c.slots then some (.slot (m.disp / 16))
    else if m.base = c.ext ∧ m.disp / 16 < c.exts then some (.ext (m.disp / 16))
    else none
  else none

/-- The 16 bytes of the table at `off`. -/
def tblAt (ws : List (BitVec 64)) (off : Nat) : BitVec 128 := ws.getD (off / 8 + 1) 0 ++ ws.getD (off / 8) 0

/-- The register an instruction writes, if any. -/
def xdst : Instr → Option XReg
  | .xop (.bin _ d _) | .xop (.shift _ d _) | .xop (.pshufd d _ _) | .xop (.pshuflw d _ _) | .xop (.pshufhw d _ _) => some d
  | .movdquLoad d _ | .movdquTbl d _ _ _ => some d
  | _ => none

section
variable (D : XDom α) (c : Cfg) (ext : Nat → Option α)

def step (e : Env α) : Instr → Option (Env α)
  | .xop (.bin .movdqa d r) => (e.reg r).map (e.setReg d)
  | .xop (.bin op d r) => match e.reg d, e.reg r with
    | some a, some b => (D.bin op a b).map (e.setReg d)
    | _, _ => none
  | .xop (.shift op d n) => ((e.reg d).bind (D.un (.shift op n))).map (e.setReg d)
  | .xop (.pshufd d r o) => ((e.reg r).bind (D.un (.pshufd o))).map (e.setReg d)
  | .xop (.pshuflw d r o) => ((e.reg r).bind (D.un (.pshuflw o))).map (e.setReg d)
  | .xop (.pshufhw d r o) => ((e.reg r).bind (D.un (.pshufhw o))).map (e.setReg d)
  | .movdquLoad d m => match c.loc m with
    | some (.slot k) => (e.slot k).map (e.setReg d)
    | some (.ext k) => (ext k).map (e.setReg d)
    | none => none
  | .movdquStore m r => match c.loc m with
    | some (.slot k) => (e.reg r).map (e.setSlot k)
    | _ => none
  | .movdquTbl d m n ws =>
    if m.base = c.tbl ∧ n = c.name ∧ ws = c.words ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ c.words.length then
      (D.const (tblAt c.words m.disp)).map (e.setReg d)
    else none
  | _ => none

def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c ext is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c ext is e post = true) : ∃ e', eval D c ext is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` of the base address `b`. -/
abbrev xAddr (b : BitVec 32) (k : Nat) : Addr := addr b (16 * k)

structure Rel (R : α → BitVec 128 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.xmm r)
  slot : ∀ k a, k < c.slots → e.slot k = some a → R a (s.mem.readW (xAddr (s.gpr c.base) k) 128)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (xAddr (s.gpr c.ext) k) 128)

structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (xAddr (s.gpr c.base) k) 16
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (xAddr (s.gpr c.ext) k) 16
  fit : (s.gpr c.base).toNat + 16 * c.slots ≤ 2 ^ 32
  sep : ∀ k < c.slots, ∀ j < c.exts, Mem.Sep (xAddr (s.gpr c.base) k) 16 (xAddr (s.gpr c.ext) j) 16
  tbl : s.gpr c.tbl = s.syms c.name

def slotRegion (c : Cfg) (s : State) : Region := ⟨(s.gpr c.base).setWidth 64, 16 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) : Ok c s' where
  slotIn k hk := by rw [hg, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [hg, hrd, hwr]; exact h.extIn k hk
  fit := by rw [hg]; exact h.fit
  sep k hk j hj := by rw [hg]; exact h.sep k hk j hj
  tbl := by rw [hg, hsy]; exact h.tbl

theorem slot_sep (b : BitVec 32) {j k : Nat} (hj : b.toNat + 16 * j + 16 ≤ 2 ^ 32)
    (hk : b.toNat + 16 * k + 16 ≤ 2 ^ 32) (h : j ≠ k) : Mem.Sep (xAddr b j) 16 (xAddr b k) 16 := by
  intro x h₁ h₂
  simp only [xAddr] at h₁ h₂
  rw [addr_eq (by omega_arith)] at h₁ h₂
  have hb : (b.setWidth 64).toNat = b.toNat := toNat_setWidth32 b
  have : j < k ∨ k < j := by omega_using [h]
  generalize b.setWidth 64 = B at *
  rcases this with h' | h' <;> bv_omega

theorem slot_contains (b : BitVec 32) {n k : Nat} (hk : k < n) (hn : b.toNat + 16 * n ≤ 2 ^ 32) :
    (⟨b.setWidth 64, 16 * n⟩ : Region).Contains (xAddr b k) (128 / 8) := by
  simp only [Region.Contains, xAddr]
  rw [Straight.addr_sub_toNat b (by omega_using [hk, hn])]
  omega_using [hk]

theorem loc_slot {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.slot k)) :
    m.base = c.base ∧ m.disp = 16 * k ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega_using [h1], h2.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_ext {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.ext k)) :
    m.base = c.ext ∧ m.disp = 16 * k ∧ k < c.exts := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega_using [h1], h2.2⟩
      · cases h
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hd : m.disp = 16 * k) :
    s.ea m = xAddr (s.gpr b) k := by
  simp only [State.ea, hb, hd, xAddr, addr]

section
variable {D : XDom α} {R : α → BitVec 128 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The slots a block stores. -/
def stored (c : Cfg) (is : List Instr) : List Nat :=
  is.filterMap fun
    | .movdquStore m _ => match c.loc m with
      | some (.slot k) => some k
      | _ => none
    | _ => none

/-- What a block of these instructions does: it changes only XMM registers
(those it writes) and slots. -/
structure Post (R : α → BitVec 128 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α) (s s' : State)
    (is : List Instr) : Prop where
  rel : Rel R c ext e' s'
  only : s' = { s with xmm := s'.xmm, mem := s'.mem }
  other : ∀ r, (is.all fun i => xdst i != some r) = true → s'.xmm r = s.xmm r
  kept : ∀ k < c.slots, k ∉ stored c is →
    s'.mem.readW (xAddr (s.gpr c.base) k) 128 = s.mem.readW (xAddr (s.gpr c.base) k) 128
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.gpr {e' : Env α} {s s' : State} {is : List Instr} (p : Post R c ext e' s s' is) : s'.gpr = s.gpr := by
  rw [p.only]
theorem Post.rd {e' : Env α} {s s' : State} {is : List Instr} (p : Post R c ext e' s s' is) : s'.rd = s.rd := by
  rw [p.only]
theorem Post.wr {e' : Env α} {s s' : State} {is : List Instr} (p : Post R c ext e' s s' is) : s'.wr = s.wr := by
  rw [p.only]
theorem Post.syms {e' : Env α} {s s' : State} {is : List Instr} (p : Post R c ext e' s s' is) : s'.syms = s.syms := by
  rw [p.only]

theorem post_setXmm {e : Env α} {s : State} (hrel : Rel R c ext e s) {d : XReg} {a : α}
    {v : BitVec 128} (hv : R a v) {i : Instr} (hi : xdst i = some d) : Post R c ext (e.setReg d a) s (s.setXmm d v) [i] where
  rel := {
    reg := fun r b h => by
      simp only [Env.setReg] at h
      show R b (if r = d then v else s.xmm r)
      split at h
      · rename_i hr; cases h; rw [ite_eq_left hr]; exact hv
      · rename_i hr; rw [ite_eq_right hr]; exact hrel.reg r b h
    slot := hrel.slot
    ext := hrel.ext }
  only := rfl
  other r hr := by
    show (if r = d then v else s.xmm r) = s.xmm r
    rw [ite_eq_right]
    rintro rfl
    simp [hi] at hr
  kept _ _ _ := rfl
  frame := Frame.refl _ _

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' [i] := by
  cases i with
  | xop o =>
    cases o with
    | bin op d r =>
      by_cases hm : op = .movdqa
      · subst hm
        simp only [step] at h
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨_, rfl, (post_setXmm hrel (hrel.reg r a ha) rfl)⟩
      · have hstep : step D c ext e (.xop (.bin op d r)) =
            match e.reg d, e.reg r with
            | some a, some b => (D.bin op a b).map (e.setReg d)
            | _, _ => none := by
          cases op <;> first | rfl | exact absurd rfl hm
        rw [hstep] at h
        split at h
        · rename_i a b ha hb
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨_, rfl, (post_setXmm hrel (hD.bin (hrel.reg d a ha) (hrel.reg r b hb) ht) rfl)⟩
        · cases h
    | shift op d n =>
      simp only [step, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨t, ⟨a, ha, ht⟩, rfl⟩ := h
      exact ⟨_, rfl, (post_setXmm hrel (hD.un (hrel.reg d a ha) ht) rfl)⟩
    | pshufd d r o =>
      simp only [step, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨t, ⟨a, ha, ht⟩, rfl⟩ := h
      exact ⟨_, rfl, (post_setXmm hrel (hD.un (hrel.reg r a ha) ht) rfl)⟩
    | pshuflw d r o =>
      simp only [step, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨t, ⟨a, ha, ht⟩, rfl⟩ := h
      exact ⟨_, rfl, (post_setXmm hrel (hD.un (hrel.reg r a ha) ht) rfl)⟩
    | pshufhw d r o =>
      simp only [step, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨t, ⟨a, ha, ht⟩, rfl⟩ := h
      exact ⟨_, rfl, (post_setXmm hrel (hD.un (hrel.reg r a ha) ht) rfl)⟩
    | _ => simp [step] at h
  | movdquLoad d m =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_slot hk
      have hea := ea_of (s := s) hb hd
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (xAddr (s.gpr c.base) k) 16 := ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨s.setXmm d (s.mem.readW (xAddr (s.gpr c.base) k) 128),
        by simp [exec, State.load128, hea, hin], ?_⟩
      exact (post_setXmm hrel (hrel.slot k a hlt ha) rfl)
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_ext hk
      have hea := ea_of (s := s) hb hd
      refine ⟨s.setXmm d (s.mem.readW (xAddr (s.gpr c.ext) k) 128),
        by simp [exec, State.load128, hea, hok.extIn k hlt], ?_⟩
      exact (post_setXmm hrel (hrel.ext k a hlt ha) rfl)
    · cases h
  | movdquStore m r =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_slot hk
      have hea := ea_of (s := s) hb hd
      have hin := hok.slotIn k hlt
      refine ⟨{ s with mem := s.mem.writeW (xAddr (s.gpr c.base) k) (s.xmm r) },
        by simp [exec, State.store128, hea, hin], ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (xAddr (s.gpr c.base) j) (128 / 8)
          (xAddr (s.gpr c.base) k) (128 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.fit; omega_using [hj, this]) (by have := hok.fit; omega_using [hlt, this]) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_⟩, rfl,
        fun _ _ => rfl, fun j hj hn => ?_, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          have e := Mem.readW_writeW_self s.mem (xAddr (s.gpr c.base) j) 16 (s.xmm r) (by decide)
          simp only at e ⊢
          rw [e]
          exact hrel.reg r a ha
        · rename_i hjk
          simp only
          rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
          exact hrel.slot j b hj hjb
      · have hs : Mem.Sep (xAddr (s.gpr c.ext) j) (128 / 8) (xAddr (s.gpr c.base) k) (128 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        simp only
        rw [Mem.readW_writeW_sep hs (by decide)]
        exact hrel.ext j b hj hjb
      · have hjk : j ≠ k := by
          rintro rfl
          simp [stored, hk] at hn
        simp only
        rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
      · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ hlt hok.fit)
    · cases h
  | movdquTbl d m n ws =>
    simp only [step] at h
    split at h
    · rename_i hc
      obtain ⟨hb, rfl, rfl, h8, hlt⟩ := hc
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨s.setXmm d (tblAt c.words m.disp), ?_, (post_setXmm hrel (hD.const ha) rfl)⟩
      have ht := hok.tbl
      rw [← hb] at ht
      simp only [exec, ht, h8, hlt, and_self, ite_true]; rfl
    · cases h
  | _ => simp [step] at h

theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' is := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, rfl, fun _ _ => rfl, fun _ _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih (hok.congr p₁.gpr p₁.rd p₁.wr p₁.syms) p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, ?_, fun r hr => ?_, fun k hk hn => ?_, ?_⟩
    · rw [p.only, p₁.only]
    · rw [List.all_cons, Bool.and_eq_true] at hr
      exact (p.other r hr.2).trans (p₁.other r (by simp [hr.1]))
    · have e : stored c (i :: is) = stored c [i] ++ stored c is := by
        simp only [stored, ← List.filterMap_append, List.singleton_append]
      rw [e, List.mem_append, not_or] at hn
      have := p.kept k hk hn.2
      rw [p₁.gpr] at this
      exact this.trans (p₁.kept k hk hn.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.gpr] at this
      exact this

end

/-- A block's parts, one after the other. -/
theorem run_append {is js : List Instr} {s s₁ : State} {o : Option State} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa js s₁ = o) : runBlock isa (is ++ js) s = o := by
  induction is generalizing s with
  | nil => cases h₁; exact h₂
  | cons i is ih =>
    rw [List.cons_append]
    show (isa.exec i s).bind _ = o
    have h₁ : (isa.exec i s).bind (runBlock isa is) = some s₁ := h₁
    cases he : isa.exec i s with
    | none => rw [he] at h₁; cases h₁
    | some u => rw [he] at h₁; exact ih h₁

/-! ## Linear layers -/

/-- Input word `i`, XORed with `v`. -/
def inX (i : Nat) (v : BitVec 128) : Nat × Nat := (v.toNat, (inWordW 128 i).2)

theorem inX_rel {k : Nat} (W : Nat → BitVec 128) {i : Nat} (hi : 128 * i + 128 ≤ 2 ^ k) (v : BitVec 128) :
    LaneRel k (assign W (2 ^ k)) (inX i v) (W i ^^^ v) := by
  have h := (lanes_sound (A := assign W (2 ^ k))).xor (inWordW_rel W hi)
    ((lanes_sound (w := 128) (k := k) (A := assign W (2 ^ k))).const (v := v) rfl) rfl
  have e : ((inWordW 128 i).1 ^^^ v.toNat, (inWordW 128 i).2 ^^^ 0) = inX i v := by
    simp [inX, inWordW]
  rw [e] at h
  exact h

/-- The slots `ins`, `(j, i, v)`, hold input word `i`, XORed with `v`. -/
def linEnv (ins : List (Nat × Nat × BitVec 128)) : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun j => (ins.find? (·.1 == j)).map fun x => inX x.2.1 x.2.2 }

/-- External word `j` is input word `xb + j`, XORed with `v`. -/
def linExt (xb : Nat) (v : BitVec 128) (j : Nat) : Option (Nat × Nat) := some (inX (xb + j) v)

/-- Each output slot `j` holds `outWordW 128 g`, below `2 ^ (128 2 ^ k)`. -/
def linPost (n k : Nat) (outs : List (Nat × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => decide (o.1 < n) && outOkW 128 k (e.slot o.1) o.2

/-- What a block of these instructions changes: XMM registers it writes, and
slots it stores. -/
structure Runs (c : Cfg) (is : List Instr) (s s' : State) : Prop where
  only : s' = { s with xmm := s'.xmm, mem := s'.mem }
  other : ∀ r, (is.all fun i => xdst i != some r) = true → s'.xmm r = s.xmm r
  kept : ∀ k < c.slots, k ∉ stored c is →
    s'.mem.readW (xAddr (s.gpr c.base) k) 128 = s.mem.readW (xAddr (s.gpr c.base) k) 128
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Runs.gpr {c : Cfg} {is : List Instr} {s s' : State} (p : Runs c is s s') : s'.gpr = s.gpr := by rw [p.only]
theorem Runs.rd {c : Cfg} {is : List Instr} {s s' : State} (p : Runs c is s s') : s'.rd = s.rd := by rw [p.only]
theorem Runs.wr {c : Cfg} {is : List Instr} {s s' : State} (p : Runs c is s s') : s'.wr = s.wr := by rw [p.only]
theorem Runs.syms {c : Cfg} {is : List Instr} {s s' : State} (p : Runs c is s s') : s'.syms = s.syms := by rw [p.only]

theorem Post.runs {R : α → BitVec 128 → Prop} {c : Cfg} {ext : Nat → Option α} {e' : Env α} {is : List Instr} {s s' : State}
    (p : Post R c ext e' s s' is) : Runs c is s s' :=
  ⟨p.only, fun r hr => p.other r hr, p.kept, p.frame⟩

/-- Two blocks, one after the other. -/
theorem Runs.trans {c : Cfg} {is js : List Instr} {s s₁ s₂ : State} (p : Runs c is s s₁) (q : Runs c js s₁ s₂) :
    Runs c (is ++ js) s s₂ where
  only := by rw [q.only, p.only]
  other r hr := by
    rw [List.all_append, Bool.and_eq_true] at hr
    exact (q.other r hr.2).trans (p.other r hr.1)
  kept k hk hn := by
    simp only [stored, List.filterMap_append, List.mem_append, not_or] at hn
    have := q.kept k hk hn.2
    rw [p.gpr] at this
    exact this.trans (p.kept k hk hn.1)
  frame := by
    have := q.frame
    simp only [slotRegion, p.gpr] at this
    exact p.frame.trans this

theorem linear_ext {k : Nat} {c : Cfg} {ext : Nat → Option (Nat × Nat)} {is : List Instr}
    {ins : List (Nat × Nat × BitVec 128)} {outs : List (Nat × (Nat → List Nat))}
    (hchk : check (ofDom (lanes 128 k)) c ext is (linEnv ins) (linPost c.slots k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 128)
    (hin : ∀ j i w, (j, i, w) ∈ ins → j < c.slots → 128 * i + 128 ≤ 2 ^ k ∧
      W i ^^^ w = s.mem.readW (xAddr (s.gpr c.base) j) 128)
    (hext : ∀ j a, j < c.exts → ext j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (xAddr (s.gpr c.ext) j) 128)) :
    ∃ s', runBlock isa is s = some s' ∧ Runs c is s s' ∧
      (∀ j g, (j, g) ∈ outs → ∀ p < 128,
        (s'.mem.readW (xAddr (s.gpr c.base) j) 128).getLsbD p = xorBits W (g p)) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c ext (linEnv ins) s := by
    refine ⟨(fun r a h => by cases h), fun j a hj h => ?_, hext⟩
    simp only [linEnv, Option.map_eq_some_iff] at h
    obtain ⟨⟨j', i, w⟩, hf, rfl⟩ := h
    have hj' : j' = j := by simpa using List.find?_some hf
    subst hj'
    obtain ⟨h1, h2⟩ := hin j' i w (List.mem_of_find?_eq_some hf) hj
    rw [← h2]; exact inX_rel W h1 w
  obtain ⟨s', hs', p⟩ := run (ofDom_sound _ lanes_sound) hok hrel he
  refine ⟨s', hs', p.runs, fun j g hjg q hq => ?_⟩
  have h := List.all_eq_true.mp hpost (j, g) hjg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := outOkW_spec h.2
  have := p.rel.slot j _ h.1 h1
  rw [p.gpr] at this
  exact outWordW_rel_of_lt h2 this q hq

/-- A linear block that the evaluator accepts, on the machine: bit `p` of
each output slot is the XOR of the input bits `g p`. -/
theorem linear_ok {k xb : Nat} {v : BitVec 128} {c : Cfg} {is : List Instr} {ins : List (Nat × Nat × BitVec 128)}
    {outs : List (Nat × (Nat → List Nat))}
    (hchk : check (ofDom (lanes 128 k)) c (linExt xb v) is (linEnv ins) (linPost c.slots k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 128)
    (hin : ∀ j i w, (j, i, w) ∈ ins → j < c.slots → 128 * i + 128 ≤ 2 ^ k ∧
      W i ^^^ w = s.mem.readW (xAddr (s.gpr c.base) j) 128)
    (hext : ∀ j < c.exts,
      128 * (xb + j) + 128 ≤ 2 ^ k ∧ W (xb + j) ^^^ v = s.mem.readW (xAddr (s.gpr c.ext) j) 128) :
    ∃ s', runBlock isa is s = some s' ∧ Runs c is s s' ∧
      (∀ j g, (j, g) ∈ outs → ∀ p < 128,
        (s'.mem.readW (xAddr (s.gpr c.base) j) 128).getLsbD p = xorBits W (g p)) :=
  linear_ext hchk hok W hin fun j a hj h => by
    simp only [linExt, Option.some.injEq] at h; subst h
    obtain ⟨h1, h2⟩ := hext j hj
    rw [← h2]; exact inX_rel W h1 v

/-- A linear block that reads no external word. -/
theorem linear_ok0 {k : Nat} {c : Cfg} {is : List Instr} {ins : List (Nat × Nat × BitVec 128)}
    {outs : List (Nat × (Nat → List Nat))}
    (hchk : check (ofDom (lanes 128 k)) c (fun _ => none) is (linEnv ins) (linPost c.slots k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 128)
    (hin : ∀ j i w, (j, i, w) ∈ ins → j < c.slots → 128 * i + 128 ≤ 2 ^ k ∧
      W i ^^^ w = s.mem.readW (xAddr (s.gpr c.base) j) 128) :
    ∃ s', runBlock isa is s = some s' ∧ Runs c is s s' ∧
      (∀ j g, (j, g) ∈ outs → ∀ p < 128,
        (s'.mem.readW (xAddr (s.gpr c.base) j) 128).getLsbD p = xorBits W (g p)) :=
  linear_ext hchk hok W hin fun _ _ _ h => by cases h

/-- A block that stores nothing leaves memory alone. -/
theorem run_mem {is : List Instr} (h : (is.all fun | .movdquStore .. => false | .xop _ | .movdquLoad .. | .movdquTbl .. => true | _ => false) = true) :
    ∀ {s s' : State}, runBlock isa is s = some s' → s'.mem = s.mem := by
  induction is with
  | nil => intro s s' hr; cases hr; rfl
  | cons i is ih =>
    intro s s' hr
    rw [List.all_cons, Bool.and_eq_true] at h
    have hr : (exec i s).bind (runBlock isa is) = some s' := hr
    obtain ⟨u, hu, hr⟩ := Option.bind_eq_some_iff.mp hr
    refine (ih h.2 hr).trans ?_
    have hi := h.1
    cases i with
    | xop o =>
      have e : u = o.exec s := (Option.some.inj hu).symm
      rw [e]
      cases o <;> rfl
    | movdquLoad d m =>
      obtain ⟨v, _, rfl⟩ := Option.map_eq_some_iff.mp hu; rfl
    | movdquTbl d m n ws =>
      have hu : exec (.movdquTbl d m n ws) s = some u := hu
      simp only [exec] at hu
      split at hu <;> cases hu
      rfl
    | _ => cases hi

/-! ## A buffer of slots -/

/-- Slot `k` (16 bytes) of the scratch buffer at `B`. -/
def W (m : Mem) (B : BitVec 32) (k : Nat) : BitVec 128 := m.readW (addr B (16 * k)) 128

/-- The `16 n` bytes of slots `[a, a + n)`. -/
abbrev slotsR (B : BitVec 32) (a n : Nat) : Region := ⟨B.setWidth 64 + BitVec.ofNat 64 (16 * a), 16 * n⟩

theorem addr16 {B : BitVec 32} {k : Nat} (h : B.toNat + 16 * k < 2 ^ 32) :
    addr B (16 * k) = B.setWidth 64 + BitVec.ofNat 64 (16 * k) := addr_eq h

/-- A slot outside the regions written keeps its value. -/
theorem W_frame {m m' : Mem} {B : BitVec 32} {rs : List Region} (hf : Frame rs m m') {k : Nat}
    (h : B.toNat + 16 * k < 2 ^ 32) (hd : ∀ r ∈ rs, Region.Disjoint (slotsR B k 1) r) : W m' B k = W m B k := by
  unfold W
  rw [addr16 h]
  exact hf.readW (Region.contains_self _ _) hd (by decide)

/-- Byte `t` of slot `k`. -/
theorem W_bit (m : Mem) {B : BitVec 32} {k t j : Nat} (h : B.toNat + 16 * k < 2 ^ 32) (ht : t < 16) (hj : j < 8) :
    (W m B k).getLsbD (8 * t + j) = (m (B.setWidth 64 + BitVec.ofNat 64 (16 * k + t))).getLsbD j := by
  have e := byte_readW m (addr B (16 * k)) (w := 128) (k := t) (by omega_arith)
  rw [addr16 h, Offset.add_ofNat_add_ofNat] at e
  rw [← e, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, W, addr16 h]

/-- The `m` slots of 16 bytes at `B` are writable, and do not wrap around. -/
structure SlotsIn (m : Nat) (s : State) (B : BitVec 32) : Prop where
  acc : ∀ k < m, InRegions s.wr (addr B (16 * k)) 16
  fit : B.toNat + 16 * m ≤ 2 ^ 32

theorem xor0 (x : BitVec 128) : x ^^^ 0 = x := BitVec.xor_zero

theorem xorBits2 (V : Nat → BitVec 128) {i t i' t' : Nat} (ht : t < 128) (ht' : t' < 128) :
    xorBits V [128 * i + t, 128 * i' + t'] = ((V i).getLsbD t ^^ (V i').getLsbD t') := by
  simp [bitOf_word V i t ht, bitOf_word V i' t' ht']

theorem xorBits_map (V : Nat → BitVec 128) (f t : Nat → Nat) (l : List Nat) (ht : ∀ i ∈ l, t i < 128) :
    xorBits V (l.map fun i => 128 * f i + t i) = l.foldr (fun i acc => (V (f i)).getLsbD (t i) ^^ acc) false := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, xorBits_cons, List.foldr_cons, bitOf_word V _ _ (ht i List.mem_cons_self),
      ih fun i hi => ht i (List.mem_cons_of_mem _ hi)]

/-! ## Expressions -/

/-- An expression of the operations on named words, as a domain: an
evaluation over it says what each result is, as a value. -/
inductive XE
  | atom (n : Nat)
  | const (v : BitVec 128)
  | un (u : Un) (e : XE)
  | bin (op : XBinOp) (a b : XE)
  deriving DecidableEq, Repr

def XE.eval (V : Nat → BitVec 128) : XE → BitVec 128
  | .atom n => V n
  | .const v => v
  | .un u e => u.eval (e.eval V)
  | .bin op a b => op.eval (a.eval V) (b.eval V)

def exprs : XDom XE where
  un u a := some (.un u a)
  bin op a b := some (.bin op a b)
  const v := some (.const v)

theorem exprs_sound (V : Nat → BitVec 128) : exprs.Sound fun e x => x = e.eval V where
  un ha h := by simp only [exprs, Option.some.injEq] at h; subst h; rw [ha]; rfl
  bin ha hb h := by simp only [exprs, Option.some.injEq] at h; subst h; rw [ha, hb]; rfl
  const h := by simp only [exprs, Option.some.injEq] at h; subst h; rfl

end VG.X86.StraightSse
