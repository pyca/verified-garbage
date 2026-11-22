module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# Byte maps in XMM registers on x86 (32-bit): what straight-line code computes of each byte

An S-box that is the AES S-box between two affine maps of a byte (Camellia's,
SM4's, SEED's) is computed in a register by `aesenclast` (its `SubBytes`,
after a `ShiftRows` that only moves the bytes) between byte maps, each two
look-ups of a nibble with `pshufb`; around it the bytes are moved by
shuffles and combined by exclusive-ors. `run` follows such code with, for
every byte of every register, what it holds as a function of the bytes the
code starts with (the registers', and those of a region of keys it only
loads from):

* a byte's value (`BV`) is the exclusive-or of input bytes (`raw`, a set as
  a bit mask), of *terms*, each a chain of byte functions (`Fn`: the AES
  S-box, a mask, the high nibble, a constant, a look-up) of an
  exclusive-or of input bytes, and of a constant;
* a linear function (a mask, the high nibble) goes into every term; any
  other function (the S-box, a look-up) is taken only of a single term or of
  input bytes, and gives one term.

`run_ok`: code that `run` follows runs, changes only the XMM registers, and
leaves in each byte the value of its expression. A proof about such code is
then a comparison of expressions, which the kernel evaluates (`BV.same`: up
to the order of the terms), and what the expressions mean is proven of them,
not of the code.

The instructions followed: `movdqa`, `pxor` (of a register with itself, zero), `pand` with a register of
constants, `pshufb` of constants (a look-up) or by constants (a shuffle),
`aesenclast`, `psrld` by 4 (only to be masked next, the high nibbles),
`psrlq` by 32, `pshufd`, `punpcklqdq`, `punpckhqdq`, and the loads of a
table an instruction carries (constants), and of 16 or 8 bytes of the keys.
`runS` also follows stores of a register to a second region, apart from the
keys (`runS_wp`): a block's stores, as expressions of what it starts with.
-/

@[expose] public section

namespace VG.X86.ByteMap

open VG VG.X86

/-! ## Bytes of a register -/

theorem byte_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byte (ofBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  rw [byte, BitVec.getLsbD_extractLsb', getLsbD_ofBytes f hi hr]
  simp only [hr, decide_true, Bool.true_and]

theorem byte_xor (a b : BitVec 128) (i : Nat) : byte (a ^^^ b) i = byte a i ^^^ byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hr, decide_true, Bool.true_and]

theorem byte_and (a b : BitVec 128) (i : Nat) : byte (a &&& b) i = byte a i &&& byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hr, decide_true, Bool.true_and]

/-- A byte of a register is a byte of one of its doublewords. -/
theorem byte_eq_dword (v : BitVec 128) (i : Nat) :
    byte v i = (dword v (i / 4)).extractLsb' (8 * (i % 4)) 8 := byte_dword v i

/-- A byte of doublewords. -/
theorem byte_ofDwords (f : Nat → BitVec 32) {i : Nat} (hi : i < 16) :
    byte (ofDwords (f 0) (f 1) (f 2) (f 3)) i = (f (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  rw [byte_eq_dword]
  exact congrArg _ (Lanes.dword_L f (by omega_arith))

/-! ## The instructions' bytes -/

theorem byte_pshufb (a b : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XBinOp.eval .pshufb a b) i =
      if (byte b i).msb then 0#8 else byte a ((byte b i).extractLsb' 0 4).toNat := by
  show byte (ofBytes fun i => if (byte b i).msb then 0#8 else byte a ((byte b i).extractLsb' 0 4).toNat) i = _
  rw [byte_ofBytes _ hi]

/-- `aesenclast`: `SubBytes` of the byte `ShiftRows` moves here, and the key's. -/
theorem byte_aesenclast (a b : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XBinOp.eval .aesenclast a b) i =
      aesSbox (byte a (i % 4 + 4 * ((i / 4 + i % 4) % 4))) ^^^ byte b i := by
  show byte (aesMapBytes aesSbox (aesShiftRows a) ^^^ b) i = _
  rw [byte_xor, aesMapBytes, byte_ofBytes _ hi, aesShiftRows, byte_ofBytes _ hi]

theorem byte_pshufd (a : BitVec 128) (o : BitVec 8) {i : Nat} (hi : i < 16) :
    byte (shufDwords a o) i = byte a (4 * (o.extractLsb' (2 * (i / 4)) 2).toNat + i % 4) := by
  have h4 : i / 4 < 4 := by omega_arith
  rw [byte_eq_dword, dword_shufDwords a o h4, byte_eq_dword a]
  have hk : (o.extractLsb' (2 * (i / 4)) 2).toNat < 4 := (o.extractLsb' (2 * (i / 4)) 2).isLt
  rw [show (4 * (o.extractLsb' (2 * (i / 4)) 2).toNat + i % 4) / 4 = (o.extractLsb' (2 * (i / 4)) 2).toNat by omega_arith,
    show (4 * (o.extractLsb' (2 * (i / 4)) 2).toNat + i % 4) % 4 = i % 4 by omega_arith]

theorem byte_punpcklqdq (a b : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XBinOp.eval .punpcklqdq a b) i = if i < 8 then byte a i else byte b (i - 8) := by
  rw [punpcklqdq_eq]
  refine (byte_ofDwords (fun k => if k < 2 then dword a k else dword b (k - 2)) hi).trans ?_
  show (if i / 4 < 2 then dword a (i / 4) else dword b (i / 4 - 2)).extractLsb' (8 * (i % 4)) 8 = _
  by_cases h : i < 8
  · rw [ite_eq_left h, ite_eq_left (show i / 4 < 2 by omega_arith), byte_eq_dword a]
  · rw [ite_eq_right h, ite_eq_right (show ¬ i / 4 < 2 by omega_arith), byte_eq_dword b,
      show (i - 8) / 4 = i / 4 - 2 by omega_arith, show (i - 8) % 4 = i % 4 by omega_arith]

theorem byte_punpckhqdq (a b : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XBinOp.eval .punpckhqdq a b) i = if i < 8 then byte a (i + 8) else byte b i := by
  rw [punpckhqdq_eq]
  refine (byte_ofDwords (fun k => if k < 2 then dword a (k + 2) else dword b k) hi).trans ?_
  show (if i / 4 < 2 then dword a (i / 4 + 2) else dword b (i / 4)).extractLsb' (8 * (i % 4)) 8 = _
  by_cases h : i < 8
  · rw [ite_eq_left h, ite_eq_left (show i / 4 < 2 by omega_arith), byte_eq_dword a,
      show (i + 8) / 4 = i / 4 + 2 by omega_arith, show (i + 8) % 4 = i % 4 by omega_arith]
  · rw [ite_eq_right h, ite_eq_right (show ¬ i / 4 < 2 by omega_arith), byte_eq_dword b]

/-- The high nibbles: a shift of the doublewords by 4, then the mask `0x0f`
of a byte. -/
theorem byte_hi4 (a m : BitVec 128) {i : Nat} (hi : i < 16) (hm : byte m i = 0x0f) :
    byte (XShiftOp.eval .psrld a 4 &&& m) i = byte a i >>> 4 := by
  rw [byte_and, hm]
  have h4 : i / 4 < 4 := by omega_arith
  rw [byte_eq_dword, dword_psrld a 4 (by decide) h4, byte_eq_dword a]
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hr, decide_true, Bool.true_and]
  have h8 : (8 : BitVec 8).toNat = 8 := rfl
  by_cases h : r < 4
  · have e1 : (0x0f : BitVec 8).getLsbD r = true := by
      have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega_arith
      rcases this with rfl | rfl | rfl | rfl <;> rfl
    have e2 : decide (4 + r < 8) = true := decide_eq_true (by omega_arith)
    rw [e1, Bool.and_true, e2, Bool.true_and]
    exact congrArg _ (by show (4 : BitVec 8).toNat + (8 * (i % 4) + r) = 8 * (i % 4) + ((4 : BitVec 8).toNat + r); omega_arith)
  · have e1 : (0x0f : BitVec 8).getLsbD r = false := by
      have : r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega_arith
      rcases this with rfl | rfl | rfl | rfl <;> rfl
    have e2 : decide (4 + r < 8) = false := decide_eq_false (by omega_arith)
    rw [e1, Bool.and_false, e2, Bool.false_and]

theorem getLsbD_qw (x : BitVec 128) (k i : Nat) :
    (qword x k).getLsbD i = (decide (i < 64) && x.getLsbD (64 * k + i)) := by
  simp only [qword, BitVec.getLsbD_extractLsb']

theorem psllq32_eq (a : BitVec 128) :
    XShiftOp.eval .psllq a 32 = (qword a 1 <<< 32) ++ (qword a 0 <<< 32) := by
  change (if 63 < (32 : BitVec 8).toNat then 0 else
    (qword a 1 <<< (32 : BitVec 8).toNat) ++ (qword a 0 <<< (32 : BitVec 8).toNat)) = _
  rw [ite_eq_right (by decide)]; rfl

theorem psrlq32_eq (a : BitVec 128) :
    XShiftOp.eval .psrlq a 32 = (qword a 1 >>> 32) ++ (qword a 0 >>> 32) := by
  change (if 63 < (32 : BitVec 8).toNat then 0 else
    (qword a 1 >>> (32 : BitVec 8).toNat) ++ (qword a 0 >>> (32 : BitVec 8).toNat)) = _
  rw [ite_eq_right (by decide)]; rfl

/-- Bit `i` of quadword `q` of `psllq` by 32. -/
theorem psllq32_bit (a : BitVec 128) {q i : Nat} (hq : q < 2) (hi : i < 64) :
    (XShiftOp.eval .psllq a 32).getLsbD (64 * q + i) = (decide (32 ≤ i) && a.getLsbD (64 * q + (i - 32))) := by
  rw [psllq32_eq, BitVec.getLsbD_append]
  have hq' : q = 0 ∨ q = 1 := by omega_arith
  rcases hq' with rfl | rfl
  · rw [ite_eq_left (by omega_arith), BitVec.getLsbD_shiftLeft, getLsbD_qw, decide_eq_true (show 64 * 0 + i < 64 by omega_arith),
      Bool.true_and]
    by_cases h : 32 ≤ i
    · rw [decide_eq_false (show ¬ 64 * 0 + i < 32 by omega_arith), decide_eq_true (show 64 * 0 + i - 32 < 64 by omega_arith),
        decide_eq_true h, Bool.not_false, Bool.true_and, Bool.true_and, Bool.true_and,
        show 64 * 0 + (64 * 0 + i - 32) = 64 * 0 + (i - 32) by omega_arith]
    · rw [decide_eq_true (show 64 * 0 + i < 32 by omega_arith), decide_eq_false h, Bool.not_true, Bool.false_and,
        Bool.false_and]
  · rw [ite_eq_right (by omega_arith), BitVec.getLsbD_shiftLeft, getLsbD_qw, decide_eq_true (show 64 * 1 + i - 64 < 64 by omega_arith),
      Bool.true_and]
    by_cases h : 32 ≤ i
    · rw [decide_eq_false (show ¬ 64 * 1 + i - 64 < 32 by omega_arith),
        decide_eq_true (show 64 * 1 + i - 64 - 32 < 64 by omega_arith),
        decide_eq_true h, Bool.not_false, Bool.true_and, Bool.true_and, Bool.true_and,
        show 64 * 1 + (64 * 1 + i - 64 - 32) = 64 * 1 + (i - 32) by omega_arith]
    · rw [decide_eq_true (show 64 * 1 + i - 64 < 32 by omega_arith), decide_eq_false h, Bool.not_true, Bool.false_and,
        Bool.false_and]

/-- Bit `i` of quadword `q` of `psrlq` by 32. -/
theorem psrlq32_bit (a : BitVec 128) {q i : Nat} (hq : q < 2) (hi : i < 64) :
    (XShiftOp.eval .psrlq a 32).getLsbD (64 * q + i) = (decide (i < 32) && a.getLsbD (64 * q + (i + 32))) := by
  rw [psrlq32_eq, BitVec.getLsbD_append]
  have hq' : q = 0 ∨ q = 1 := by omega_arith
  rcases hq' with rfl | rfl
  · rw [ite_eq_left (by omega_arith), BitVec.getLsbD_ushiftRight, getLsbD_qw,
      show 64 * 0 + (32 + (64 * 0 + i)) = 64 * 0 + (i + 32) by omega_arith]
    by_cases h : i < 32
    · rw [decide_eq_true (show 32 + (64 * 0 + i) < 64 by omega_arith), decide_eq_true h]
    · rw [decide_eq_false (show ¬ 32 + (64 * 0 + i) < 64 by omega_arith), decide_eq_false h]
  · rw [ite_eq_right (by omega_arith), BitVec.getLsbD_ushiftRight, getLsbD_qw,
      show 64 * 1 + (32 + (64 * 1 + i - 64)) = 64 * 1 + (i + 32) by omega_arith]
    by_cases h : i < 32
    · rw [decide_eq_true (show 32 + (64 * 1 + i - 64) < 64 by omega_arith), decide_eq_true h]
    · rw [decide_eq_false (show ¬ 32 + (64 * 1 + i - 64) < 64 by omega_arith), decide_eq_false h]

/-- `psrlq` by 32 moves the high four bytes of each quadword down. -/
theorem byte_psrlq32 (a : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XShiftOp.eval .psrlq a 32) i = if i % 8 < 4 then byte a (i + 4) else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  unfold byte
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
    show 8 * i + r = 64 * (i / 8) + (8 * (i % 8) + r) by omega_arith,
    psrlq32_bit a (show i / 8 < 2 by omega_arith) (show 8 * (i % 8) + r < 64 by omega_arith)]
  by_cases h : i % 8 < 4
  · rw [ite_eq_left h, decide_eq_true (show 8 * (i % 8) + r < 32 by omega_arith), Bool.true_and,
      BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
    exact congrArg _ (by omega_arith)
  · rw [ite_eq_right h, decide_eq_false (show ¬ 8 * (i % 8) + r < 32 by omega_arith), Bool.false_and]
    exact (BitVec.getLsbD_zero ..).symm

/-! ## A byte's value -/

/-- A function of a byte. -/
inductive Fn
  /-- The AES S-box (FIPS 197 §5.1.1). -/
  | aes
  | and (c : BitVec 8)
  /-- The high nibble. -/
  | hi4
  | xorc (c : BitVec 8)
  /-- `pshufb`'s look-up in the 16 bytes `t`: zero if bit 7 is set, else
  the byte at the low nibble. -/
  | look (t : BitVec 128)
  deriving DecidableEq

def Fn.eval : Fn → BitVec 8 → BitVec 8
  | .aes, b => aesSbox b
  | .and c, b => b &&& c
  | .hi4, b => b >>> 4
  | .xorc c, b => b ^^^ c
  | .look t, b => if b.msb then 0#8 else byte t (b.extractLsb' 0 4).toNat

/-- The functions of a chain, the first applied last. -/
def chain : List Fn → BitVec 8 → BitVec 8
  | [], b => b
  | f :: fs, b => f.eval (chain fs b)

/-- A chain of functions of the exclusive-or of the input bytes `vars` (a set
of their numbers, as a bit mask). -/
structure Term where
  fs : List Fn
  vars : Nat
  deriving DecidableEq

/-- The exclusive-or of the input bytes `raw`, of terms and of a constant. -/
structure BV where
  raw : Nat
  terms : List Term
  const : BitVec 8
  deriving DecidableEq

/-- Input bytes are numbered below this. -/
def nvars : Nat := 1024

/-- The exclusive-or of the input bytes of `m` numbered below `n`. -/
def mask (env : Nat → BitVec 8) (m : Nat) : Nat → BitVec 8
  | 0 => 0#8
  | n + 1 => mask env m n ^^^ (if m.testBit n then env n else 0#8)

def Term.eval (env : Nat → BitVec 8) (t : Term) : BitVec 8 := chain t.fs (mask env t.vars nvars)

def sum (env : Nat → BitVec 8) : List Term → BitVec 8
  | [] => 0#8
  | t :: ts => t.eval env ^^^ sum env ts

def BV.eval (env : Nat → BitVec 8) (v : BV) : BitVec 8 := mask env v.raw nvars ^^^ sum env v.terms ^^^ v.const

section
variable (env : Nat → BitVec 8)

theorem mask_xor (a b n : Nat) : mask env (a ^^^ b) n = mask env a n ^^^ mask env b n := by
  induction n with
  | zero => simp only [mask, BitVec.xor_zero]
  | succ n ih =>
    simp only [mask, ih, Nat.testBit_xor]
    cases Nat.testBit a n <;> cases Nat.testBit b n
    · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    · simp only [Bool.false_bne, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]; ac_rfl
    · simp only [Bool.bne_false, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]; ac_rfl
    · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
      rw [show mask env a n ^^^ env n ^^^ (mask env b n ^^^ env n) =
        mask env a n ^^^ mask env b n ^^^ (env n ^^^ env n) by ac_rfl, BitVec.xor_self, BitVec.xor_zero]

theorem mask_zero (n : Nat) : mask env 0 n = 0#8 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mask, ih, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]

theorem mask_bit_le {i n : Nat} (h : n ≤ i) : mask env (2 ^ i) n = 0#8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hne : i ≠ n := by omega_arith
    simp only [mask, ih (by omega_arith), Nat.testBit_two_pow, hne, decide_false, Bool.false_eq_true, ↓reduceIte,
      BitVec.xor_zero]

theorem mask_bit {i n : Nat} (h : i < n) : mask env (2 ^ i) n = env i := by
  induction n with
  | zero => cases h
  | succ n ih =>
    by_cases hi : i = n
    · subst hi
      simp only [mask, mask_bit_le env (Nat.le_refl i), Nat.testBit_two_pow, decide_true, ↓reduceIte, BitVec.zero_xor]
    · simp only [mask, ih (by omega_arith), Nat.testBit_two_pow, hi, decide_false, Bool.false_eq_true, ↓reduceIte,
        BitVec.xor_zero]

theorem sum_append (a b : List Term) : sum env (a ++ b) = sum env a ^^^ sum env b := by
  induction a with
  | nil => simp only [List.nil_append, sum, BitVec.zero_xor]
  | cons t ts ih => simp only [List.cons_append, sum, ih, BitVec.xor_assoc]

theorem sum_perm {a b : List Term} (h : a.Perm b) : sum env a = sum env b := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [sum, ih]
  | swap t u l => simp only [sum]; ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end

def BV.zero : BV := ⟨0, [], 0#8⟩
def BV.cst (c : BitVec 8) : BV := ⟨0, [], c⟩
/-- Input byte `i`. -/
def BV.var (i : Nat) : BV := ⟨2 ^ i, [], 0#8⟩
def BV.xor (a b : BV) : BV := ⟨a.raw ^^^ b.raw, a.terms ++ b.terms, a.const ^^^ b.const⟩

/-- Whether `g` distributes over exclusive-or. -/
def Fn.linear : Fn → Bool
  | .and _ | .hi4 => true
  | _ => false

/-- A linear function of a value: of each of its terms, and of its input
bytes as one term. -/
def BV.lin (g : Fn) (v : BV) : BV :=
  ⟨0, (if v.raw = 0 then [] else [⟨[g], v.raw⟩]) ++ v.terms.map (fun t => ⟨g :: t.fs, t.vars⟩), g.eval v.const⟩

/-- A constant under a function, as a chain. -/
def cst? (c : BitVec 8) : List Fn := if c = 0#8 then [] else [.xorc c]

/-- A function of a value that is input bytes and a constant, or one term
and a constant: one term. -/
def BV.app (f : Fn) (v : BV) : Option BV :=
  match v.terms with
  | [] => if v.raw = 0 then some (.cst (f.eval v.const)) else some ⟨0, [⟨f :: cst? v.const, v.raw⟩], 0#8⟩
  | [t] => if v.raw = 0 then some ⟨0, [⟨f :: (cst? v.const ++ t.fs), t.vars⟩], 0#8⟩ else none
  | _ => none

def BV.isConst (v : BV) : Bool := v.raw == 0 && v.terms.isEmpty

/-- The same value, up to the order of the terms. -/
def BV.same (a b : BV) : Bool := a.raw == b.raw && a.const == b.const && a.terms.isPerm b.terms

section
variable (env : Nat → BitVec 8)

theorem BV.zero_eval : BV.zero.eval env = 0#8 := by
  simp only [BV.eval, BV.zero, mask_zero, sum, BitVec.xor_zero]

theorem BV.cst_eval (c : BitVec 8) : (BV.cst c).eval env = c := by
  simp only [BV.eval, BV.cst, mask_zero, sum, BitVec.zero_xor]

theorem BV.var_eval {i : Nat} (h : i < nvars) : (BV.var i).eval env = env i := by
  simp only [BV.eval, BV.var, mask_bit env h, sum, BitVec.xor_zero]

theorem BV.xor_eval (a b : BV) : (a.xor b).eval env = a.eval env ^^^ b.eval env := by
  simp only [BV.eval, BV.xor, mask_xor, sum_append]; ac_rfl

theorem Fn.lin_xor {g : Fn} (h : g.linear = true) (a b : BitVec 8) : g.eval (a ^^^ b) = g.eval a ^^^ g.eval b := by
  cases g with
  | and c =>
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [Fn.eval, BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]
  | hi4 => exact BitVec.ushiftRight_xor_distrib a b 4
  | _ => cases h

theorem Fn.lin_zero {g : Fn} (h : g.linear = true) : g.eval 0#8 = 0#8 := by
  cases g with
  | and c => exact BitVec.zero_and
  | hi4 => rfl
  | _ => cases h

theorem sum_lin {g : Fn} (h : g.linear = true) (ts : List Term) :
    sum env (ts.map fun t => ⟨g :: t.fs, t.vars⟩) = g.eval (sum env ts) := by
  induction ts with
  | nil => exact (Fn.lin_zero h).symm
  | cons t ts ih => simp only [List.map_cons, sum, ih, Fn.lin_xor h]; rfl

theorem BV.lin_eval {g : Fn} (h : g.linear = true) (v : BV) : (v.lin g).eval env = g.eval (v.eval env) := by
  simp only [BV.eval, BV.lin, mask_zero, sum_append, sum_lin env h, Fn.lin_xor h, BitVec.zero_xor]
  refine congrArg (· ^^^ g.eval v.const) (congrArg (· ^^^ g.eval (sum env v.terms)) ?_)
  by_cases h0 : v.raw = 0
  · rw [ite_eq_left h0, h0, mask_zero, Fn.lin_zero h]; rfl
  · rw [ite_eq_right h0]; simp only [sum, BitVec.xor_zero]; rfl

theorem chain_cst (c : BitVec 8) (fs : List Fn) (b : BitVec 8) : chain (cst? c ++ fs) b = chain fs b ^^^ c := by
  unfold cst?
  by_cases h : c = 0#8
  · rw [ite_eq_left h, h, BitVec.xor_zero]; rfl
  · rw [ite_eq_right h]; rfl

theorem BV.app_eval {f : Fn} {v w : BV} (h : v.app f = some w) : w.eval env = f.eval (v.eval env) := by
  unfold BV.app at h
  split at h
  · rename_i ht
    by_cases h0 : v.raw = 0
    · rw [ite_eq_left h0] at h; cases h
      rw [BV.cst_eval, BV.eval, ht, h0, mask_zero, sum, BitVec.zero_xor, BitVec.zero_xor]
    · rw [ite_eq_right h0] at h; cases h
      simp only [BV.eval, mask_zero, sum, Term.eval, BitVec.xor_zero, BitVec.zero_xor, ht]
      show f.eval (chain (cst? v.const) _) = _
      rw [← List.append_nil (cst? v.const), chain_cst]; rfl
  · rename_i t ht
    by_cases h0 : v.raw = 0
    · rw [ite_eq_left h0] at h; cases h
      simp only [BV.eval, mask_zero, sum, Term.eval, BitVec.xor_zero, BitVec.zero_xor, ht, h0]
      show f.eval (chain (cst? v.const ++ t.fs) _) = _
      rw [chain_cst]
    · rw [ite_eq_right h0] at h; cases h
  · cases h

theorem BV.isConst_eval {v : BV} (h : v.isConst = true) : v.eval env = v.const := by
  simp only [BV.isConst, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  rw [BV.eval, h.1, h.2, mask_zero, sum, BitVec.zero_xor, BitVec.zero_xor]

theorem BV.same_eval {a b : BV} (h : a.same b = true) : a.eval env = b.eval env := by
  simp only [BV.same, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at h
  rw [BV.eval, BV.eval, h.1.1, h.1.2, sum_perm env h.2]

end

/-! ## Registers -/

/-- A register's sixteen bytes; `sh`: the register holds them with its
doublewords shifted right by 4 (after `psrld`, before the mask that makes
them the high nibbles). -/
structure RV where
  sh : Bool
  bs : List BV

def get (bs : List BV) (i : Nat) : BV := bs.getD i .zero
def bytes (f : Nat → BV) : List BV := (List.range 16).map f

theorem get_bytes (f : Nat → BV) {i : Nat} (hi : i < 16) : get (bytes f) i = f i := by
  simp only [get, bytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

/-- Sixteen bytes, if each is defined. -/
def bytes? (f : Nat → Option BV) : Option (List BV) :=
  if (List.range 16).all (fun i => (f i).isSome) = true then some (bytes fun i => (f i).getD .zero) else none

theorem bytes?_some {f : Nat → Option BV} {l : List BV} (h : bytes? f = some l) {i : Nat} (hi : i < 16) :
    f i = some (get l i) := by
  unfold bytes? at h
  split at h <;> [rename_i ha; cases h]
  cases h
  rw [get_bytes _ hi]
  have := List.all_eq_true.mp ha i (List.mem_range.mpr hi)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
  rw [hv]; rfl

def allConst (bs : List BV) : Bool := (List.range 16).all fun i => (get bs i).isConst

theorem allConst_eval (env : Nat → BitVec 8) {bs : List BV} (h : allConst bs = true) {i : Nat} (hi : i < 16) :
    (get bs i).eval env = (get bs i).const :=
  BV.isConst_eval env (List.all_eq_true.mp h i (List.mem_range.mpr hi))

/-- The eight registers. -/
structure Regs where
  x0 : RV
  x1 : RV
  x2 : RV
  x3 : RV
  x4 : RV
  x5 : RV
  x6 : RV
  x7 : RV

def Regs.get : Regs → XReg → RV
  | ⟨a, _, _, _, _, _, _, _⟩, .xmm0 => a
  | ⟨_, a, _, _, _, _, _, _⟩, .xmm1 => a
  | ⟨_, _, a, _, _, _, _, _⟩, .xmm2 => a
  | ⟨_, _, _, a, _, _, _, _⟩, .xmm3 => a
  | ⟨_, _, _, _, a, _, _, _⟩, .xmm4 => a
  | ⟨_, _, _, _, _, a, _, _⟩, .xmm5 => a
  | ⟨_, _, _, _, _, _, a, _⟩, .xmm6 => a
  | ⟨_, _, _, _, _, _, _, a⟩, .xmm7 => a

def Regs.set : Regs → XReg → RV → Regs
  | ⟨_, b, c, d, e, f, g, h⟩, .xmm0, v => ⟨v, b, c, d, e, f, g, h⟩
  | ⟨a, _, c, d, e, f, g, h⟩, .xmm1, v => ⟨a, v, c, d, e, f, g, h⟩
  | ⟨a, b, _, d, e, f, g, h⟩, .xmm2, v => ⟨a, b, v, d, e, f, g, h⟩
  | ⟨a, b, c, _, e, f, g, h⟩, .xmm3, v => ⟨a, b, c, v, e, f, g, h⟩
  | ⟨a, b, c, d, _, f, g, h⟩, .xmm4, v => ⟨a, b, c, d, v, f, g, h⟩
  | ⟨a, b, c, d, e, _, g, h⟩, .xmm5, v => ⟨a, b, c, d, e, v, g, h⟩
  | ⟨a, b, c, d, e, f, _, h⟩, .xmm6, v => ⟨a, b, c, d, e, f, v, h⟩
  | ⟨a, b, c, d, e, f, g, _⟩, .xmm7, v => ⟨a, b, c, d, e, f, g, v⟩

theorem Regs.get_set (ρ : Regs) (r r' : XReg) (v : RV) :
    (ρ.set r v).get r' = if r' = r then v else ρ.get r' := by
  cases ρ; cases r <;> cases r' <;> rfl

/-- The table's base register and name, and the keys' register and length
in bytes: byte `o` of the keys is input byte `128 + o`; byte `i` of
register `k`, on entry, input byte `16 k + i`. -/
structure Params where
  tb : Reg
  name : String
  kreg : Reg
  klen : Nat

/-- The registers on entry. -/
def Regs.init : Regs :=
  let r := fun (k : Nat) => (⟨false, bytes fun i => .var (16 * k + i)⟩ : RV)
  ⟨r 0, r 1, r 2, r 3, r 4, r 5, r 6, r 7⟩

/-- A plain register's bytes. -/
def plain (ρ : Regs) (r : XReg) : Option (List BV) := if (ρ.get r).sh = true then none else some (ρ.get r).bs

/-- The byte `ShiftRows` moves to position `i`. -/
def srow (i : Nat) : Nat := i % 4 + 4 * ((i / 4 + i % 4) % 4)

/-- The 16 constants of `bs`, as a register. -/
def tableOf (bs : List BV) : BitVec 128 := ofBytes fun i => (get bs i).const

/-- What an instruction does to the registers' expressions; `none` for an
instruction, or operands, this does not follow. -/
def step (p : Params) (ρ : Regs) : Instr → Option Regs
  | .movdquTbl d m n ws =>
    if m.base = p.tb ∧ n = p.name ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ ws.length then
      some (ρ.set d ⟨false, bytes fun i => .cst ((ws.getD (m.disp / 8 + i / 8) 0).extractLsb' (8 * (i % 8)) 8)⟩)
    else none
  | .movdquLoad d m =>
    if m.base = p.kreg ∧ m.disp + 16 ≤ p.klen ∧ p.klen + 128 ≤ nvars then
      some (ρ.set d ⟨false, bytes fun i => .var (128 + m.disp + i)⟩)
    else none
  | .movqLoad d m =>
    if m.base = p.kreg ∧ m.disp + 16 ≤ p.klen ∧ p.klen + 128 ≤ nvars then
      some (ρ.set d ⟨false, bytes fun i => if i < 8 then .var (128 + m.disp + i) else .zero⟩)
    else none
  | .xop (.bin .movdqa a b) => (plain ρ b).map fun y => ρ.set a ⟨false, y⟩
  | .xop (.bin .pxor a b) =>
    if a = b then some (ρ.set a ⟨false, bytes fun _ => .zero⟩)
    else (plain ρ a).bind fun x => (plain ρ b).map fun y => ρ.set a ⟨false, bytes fun i => (get x i).xor (get y i)⟩
  | .xop (.bin .pand a b) =>
    (plain ρ b).bind fun y =>
      if (ρ.get a).sh = true then
        if (List.range 16).all (fun i => (get y i).isConst && (get y i).const == 0x0f#8) = true then
          some (ρ.set a ⟨false, bytes fun i => (get (ρ.get a).bs i).lin .hi4⟩)
        else none
      else if allConst y = true then
        some (ρ.set a ⟨false, bytes fun i => (get (ρ.get a).bs i).lin (.and (get y i).const)⟩)
      else if allConst (ρ.get a).bs = true then
        some (ρ.set a ⟨false, bytes fun i => (get y i).lin (.and (get (ρ.get a).bs i).const)⟩)
      else none
  | .xop (.shift .psrld a n) =>
    if n = 4 then (plain ρ a).map fun x => ρ.set a ⟨true, x⟩ else none
  | .xop (.shift .psrlq a n) =>
    if n = 32 then (plain ρ a).map fun x => ρ.set a ⟨false, bytes fun i => if i % 8 < 4 then get x (i + 4) else .zero⟩
    else none
  | .xop (.bin .pshufb a b) =>
    (plain ρ a).bind fun x => (plain ρ b).bind fun y =>
      if allConst y = true then
        some (ρ.set a ⟨false, bytes fun i =>
          if (get y i).const.msb = true then .zero else get x ((get y i).const.extractLsb' 0 4).toNat⟩)
      else if allConst x = true then
        (bytes? fun i => (get y i).app (.look (tableOf x))).map fun l => ρ.set a ⟨false, l⟩
      else none
  | .xop (.bin .aesenclast a b) =>
    (plain ρ a).bind fun x => (plain ρ b).bind fun y =>
      (bytes? fun i => ((get x (srow i)).app .aes).map fun v => v.xor (get y i)).map fun l => ρ.set a ⟨false, l⟩
  | .xop (.pshufd d r o) =>
    (plain ρ r).map fun y => ρ.set d ⟨false, bytes fun i => get y (4 * (o.extractLsb' (2 * (i / 4)) 2).toNat + i % 4)⟩
  | .xop (.bin .punpcklqdq a b) =>
    (plain ρ a).bind fun x => (plain ρ b).map fun y =>
      ρ.set a ⟨false, bytes fun i => if i < 8 then get x i else get y (i - 8)⟩
  | .xop (.bin .punpckhqdq a b) =>
    (plain ρ a).bind fun x => (plain ρ b).map fun y =>
      ρ.set a ⟨false, bytes fun i => if i < 8 then get x (i + 8) else get y i⟩
  | _ => none

/-- The expressions after a block. -/
def run (p : Params) : Regs → List Instr → Option Regs
  | ρ, [] => some ρ
  | ρ, i :: is =>
    match step p ρ i with
    | some ρ' => run p ρ' is
    | none => none

/-! ## What the registers hold -/

/-- What a register holds is what its expression says. -/
def Holds (env : Nat → BitVec 8) (rv : RV) (x : BitVec 128) : Prop :=
  if rv.sh = true then ∃ a, x = XShiftOp.eval .psrld a 4 ∧ ∀ i < 16, byte a i = (get rv.bs i).eval env
  else ∀ i < 16, byte x i = (get rv.bs i).eval env

/-- The state the expressions `ρ` describe, with the input bytes `env`: the
table's register holds its address, the keys are readable and hold their
input bytes, and every register what its expression says. -/
structure Rel (p : Params) (env : Nat → BitVec 8) (ρ : Regs) (s : State) : Prop where
  tb : s.gpr p.tb = s.syms p.name
  key : ∀ o i, o + 16 ≤ p.klen → i < 16 →
    s.mem (addr (s.gpr p.kreg) o + BitVec.ofNat 64 i) = env (128 + o + i)
  acc : ∀ o, o + 16 ≤ p.klen → InRegions (s.rd ++ s.wr) (addr (s.gpr p.kreg) o) 16
  regs : ∀ r, Holds env (ρ.get r) (s.xmm r)

/-- `s'` is `s` but for its XMM registers. -/
def Same (s s' : State) : Prop := ∃ f, s' = { s with xmm := f }

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c := by
  obtain ⟨f, rfl⟩ := h₁
  obtain ⟨g, rfl⟩ := h₂
  exact ⟨g, rfl⟩

section
variable {p : Params} {env : Nat → BitVec 8} {ρ : Regs} {s : State}

theorem holds_plain {bs : List BV} {x : BitVec 128} :
    Holds env ⟨false, bs⟩ x ↔ ∀ i < 16, byte x i = (get bs i).eval env := by
  simp only [Holds, Bool.false_eq_true, ↓reduceIte]

theorem Rel.plain (hr : Rel p env ρ s) {r : XReg} {y : List BV} (h : plain ρ r = some y) :
    ∀ i < 16, byte (s.xmm r) i = (get y i).eval env := by
  unfold ByteMap.plain at h
  split at h <;> [cases h; rename_i hs]
  cases h
  have := hr.regs r
  rw [Holds, ite_eq_right hs] at this
  exact this

theorem Rel.setH (hr : Rel p env ρ s) (d : XReg) {rv : RV} {v : BitVec 128} (h : Holds env rv v) :
    Rel p env (ρ.set d rv) (s.setXmm d v) := by
  refine ⟨hr.tb, hr.key, hr.acc, fun r => ?_⟩
  rw [Regs.get_set]
  show Holds env _ (if r = d then v else s.xmm r)
  by_cases e : r = d
  · rw [ite_eq_left e, ite_eq_left e]; exact h
  · rw [ite_eq_right e, ite_eq_right e]; exact hr.regs r

theorem Rel.set (hr : Rel p env ρ s) (d : XReg) {bs : List BV} {v : BitVec 128}
    (h : ∀ i < 16, byte v i = (get bs i).eval env) : Rel p env (ρ.set d ⟨false, bs⟩) (s.setXmm d v) :=
  hr.setH d (holds_plain.mpr h)

theorem srow_lt (i : Nat) : srow i < 16 := by unfold srow; omega_arith

/-- A byte of two words. -/
theorem byte_append (hi lo : BitVec 64) {i : Nat} (h : i < 16) :
    byte (hi ++ lo) i = (if i < 8 then lo else hi).extractLsb' (8 * (i % 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hr, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · rw [ite_eq_left h8, ite_eq_left (show 8 * i + r < 64 by omega_arith), show i % 8 = i by omega_arith]
  · rw [ite_eq_right h8, ite_eq_right (show ¬ 8 * i + r < 64 by omega_arith)]
    exact congrArg _ (by omega_arith)

theorem contains_8 {rs : List Region} {a : Addr} (h : InRegions rs a 16) : InRegions rs a 8 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega_arith⟩

/-- An instruction `step` follows runs, writes one XMM register, and leaves
what the expressions say. -/
theorem step_ok {i : Instr} {ρ' : Regs} (hr : Rel p env ρ s) (hs : step p ρ i = some ρ') :
    ∃ d v, exec i s = some (s.setXmm d v) ∧ Rel p env ρ' (s.setXmm d v) := by
  unfold step at hs
  split at hs
  · -- movdquTbl
    rename_i d m n ws
    split at hs <;> [rename_i hc; cases hs]
    cases hs
    obtain ⟨hb, hn, h8, hl⟩ := hc
    refine ⟨d, ws.getD (m.disp / 8 + 1) 0 ++ ws.getD (m.disp / 8) 0, ?_, hr.set d fun i hi => ?_⟩
    · show (if s.gpr m.base = s.syms n ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ ws.length then _ else none) = _
      rw [ite_eq_left ⟨by rw [hb, hn]; exact hr.tb, h8, hl⟩]
    · rw [get_bytes _ hi, BV.cst_eval, byte_append _ _ hi]
      by_cases h : i < 8
      · rw [ite_eq_left h, show i / 8 = 0 by omega_arith]; rfl
      · rw [ite_eq_right h, show i / 8 = 1 by omega_arith]
  · -- movdquLoad
    rename_i d m
    split at hs <;> [rename_i hc; cases hs]
    cases hs
    obtain ⟨hb, hl, hn⟩ := hc
    have ha := hr.acc m.disp hl
    refine ⟨d, s.mem.readW (addr (s.gpr p.kreg) m.disp) 128, ?_, hr.set d fun i hi => ?_⟩
    · show (s.load128 (addr (s.gpr m.base) m.disp)).map _ = _
      rw [hb, State.load128, ite_eq_left ha]; rfl
    · rw [get_bytes _ hi, BV.var_eval env (by omega_using [hn, hl, hi]), ← hr.key m.disp i hl hi]
      exact byte_readW _ _ (by omega_arith)
  · -- movqLoad
    rename_i d m
    split at hs <;> [rename_i hc; cases hs]
    cases hs
    obtain ⟨hb, hl, hn⟩ := hc
    have ha := contains_8 (hr.acc m.disp hl)
    refine ⟨d, (0 : BitVec 64) ++ s.mem.readW (addr (s.gpr p.kreg) m.disp) 64, ?_, hr.set d fun i hi => ?_⟩
    · show (s.load64 (addr (s.gpr m.base) m.disp)).map _ = _
      rw [hb, State.load64, ite_eq_left ha]; rfl
    · rw [get_bytes _ hi, byte_append _ _ hi]
      by_cases h : i < 8
      · rw [ite_eq_left h, ite_eq_left h, BV.var_eval env (by omega_using [hn, hl, hi]), ← hr.key m.disp i hl hi,
          show i % 8 = i by omega_arith]
        exact byte_readW _ _ (by omega_arith)
      · rw [ite_eq_right h, ite_eq_right h, BV.zero_eval]
        apply BitVec.eq_of_getLsbD_eq; intro r _
        simp
  · -- movdqa
    rename_i a b
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨a, _, rfl, hr.set a (hr.plain hy)⟩
  · -- pxor
    rename_i a b
    split at hs
    · rename_i hab
      cases hs
      refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
      rw [get_bytes _ hi, BV.zero_eval]
      show byte (s.xmm a ^^^ s.xmm b) i = _
      rw [hab, BitVec.xor_self]
      apply BitVec.eq_of_getLsbD_eq; intro r _
      simp [byte]
    · obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs
      refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
      rw [get_bytes _ hi, BV.xor_eval, ← hr.plain hx i hi, ← hr.plain hy i hi]
      exact byte_xor _ _ _
  · -- pand
    rename_i a b
    obtain ⟨y, hy, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hY := hr.plain hy
    split at hs
    · rename_i hsh
      split at hs <;> [rename_i hc; cases hs]
      cases hs
      have hA := hr.regs a
      rw [Holds, ite_eq_left hsh] at hA
      obtain ⟨A, hA, hb⟩ := hA
      refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
      have hci := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true, beq_iff_eq] at hci
      rw [get_bytes _ hi, BV.lin_eval env rfl, ← hb i hi]
      show byte (s.xmm a &&& s.xmm b) i = _
      rw [hA]
      exact byte_hi4 A _ hi (by rw [hY i hi, BV.isConst_eval env hci.1, hci.2]; rfl)
    · rename_i hsh
      have hX : ∀ i < 16, byte (s.xmm a) i = (get (ρ.get a).bs i).eval env := by
        have := hr.regs a
        rw [Holds, ite_eq_right hsh] at this
        exact this
      split at hs
      · rename_i hc
        cases hs
        refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
        rw [get_bytes _ hi, BV.lin_eval env rfl, ← hX i hi, ← allConst_eval env hc hi, ← hY i hi]
        exact byte_and _ _ _
      · split at hs <;> [rename_i hc; cases hs]
        cases hs
        refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
        rw [get_bytes _ hi, BV.lin_eval env rfl, ← hY i hi, ← allConst_eval env hc hi, ← hX i hi]
        exact (byte_and _ _ _).trans (BitVec.and_comm _ _)
  · -- psrld
    rename_i a n
    split at hs <;> [rename_i hn; cases hs]
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hs
    subst hn
    refine ⟨a, _, rfl, hr.setH a ?_⟩
    rw [Holds, ite_eq_left rfl]
    exact ⟨s.xmm a, rfl, hr.plain hx⟩
  · -- psrlq
    rename_i a n
    split at hs <;> [rename_i hn; cases hs]
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hs
    subst hn
    refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
    rw [get_bytes _ hi]
    show byte (XShiftOp.eval .psrlq (s.xmm a) 32) i = _
    rw [byte_psrlq32 _ hi]
    by_cases h : i % 8 < 4
    · rw [ite_eq_left h, ite_eq_left h]; exact hr.plain hx _ (by omega_arith)
    · rw [ite_eq_right h, ite_eq_right h, BV.zero_eval]
  · -- pshufb
    rename_i a b
    obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨y, hy, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hX := hr.plain hx
    have hY := hr.plain hy
    split at hs
    · rename_i hc
      cases hs
      refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
      rw [get_bytes _ hi]
      show byte (XBinOp.eval .pshufb (s.xmm a) (s.xmm b)) i = _
      rw [byte_pshufb _ _ hi, hY i hi, allConst_eval env hc hi]
      by_cases hm : (get y i).const.msb = true
      · rw [ite_eq_left hm, ite_eq_left hm, BV.zero_eval]
      · rw [ite_eq_right hm, ite_eq_right hm]
        exact hX _ (BitVec.isLt _)
    · split at hs <;> [rename_i hc; cases hs]
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hs
      refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
      rw [BV.app_eval env (bytes?_some hl hi)]
      show byte (XBinOp.eval .pshufb (s.xmm a) (s.xmm b)) i = _
      rw [byte_pshufb _ _ hi, hY i hi]
      show _ = if ((get y i).eval env).msb then 0#8 else byte (tableOf x) (((get y i).eval env).extractLsb' 0 4).toNat
      by_cases hm : ((get y i).eval env).msb = true
      · rw [ite_eq_left hm, ite_eq_left hm]
      · rw [ite_eq_right hm, ite_eq_right hm, tableOf, byte_ofBytes _ (BitVec.isLt _), hX _ (BitVec.isLt _),
          allConst_eval env hc (BitVec.isLt _)]
  · -- aesenclast
    rename_i a b
    obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨y, hy, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
    obtain ⟨v, hv, e⟩ := Option.map_eq_some_iff.mp (bytes?_some hl hi)
    rw [← e, BV.xor_eval, BV.app_eval env hv, ← hr.plain hx _ (srow_lt i), ← hr.plain hy i hi]
    exact byte_aesenclast _ _ hi
  · -- pshufd
    rename_i d r o
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨d, _, rfl, hr.set d fun i hi => ?_⟩
    have hk : (o.extractLsb' (2 * (i / 4)) 2).toNat < 4 := (o.extractLsb' (2 * (i / 4)) 2).isLt
    rw [get_bytes _ hi, ← hr.plain hy _ (by omega_using [hk] : 4 * (o.extractLsb' (2 * (i / 4)) 2).toNat + i % 4 < 16)]
    exact byte_pshufd _ _ hi
  · -- punpcklqdq
    rename_i a b
    obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
    rw [get_bytes _ hi]
    show byte (XBinOp.eval .punpcklqdq (s.xmm a) (s.xmm b)) i = _
    rw [byte_punpcklqdq _ _ hi]
    by_cases h : i < 8
    · rw [ite_eq_left h, ite_eq_left h]; exact hr.plain hx i hi
    · rw [ite_eq_right h, ite_eq_right h]; exact hr.plain hy _ (by omega_arith)
  · -- punpckhqdq
    rename_i a b
    obtain ⟨x, hx, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨a, _, rfl, hr.set a fun i hi => ?_⟩
    rw [get_bytes _ hi]
    show byte (XBinOp.eval .punpckhqdq (s.xmm a) (s.xmm b)) i = _
    rw [byte_punpckhqdq _ _ hi]
    by_cases h : i < 8
    · rw [ite_eq_left h, ite_eq_left h]; exact hr.plain hx _ (by omega_arith)
    · rw [ite_eq_right h, ite_eq_right h]; exact hr.plain hy i hi
  · cases hs

/-- Code `run` follows runs, changes only the XMM registers, and leaves what
the expressions say. -/
theorem run_wp {is : List Instr} {ρ' : Regs} (hr : Rel p env ρ s) (hs : run p ρ is = some ρ')
    {Q : State → Prop} (hQ : ∀ s', Rel p env ρ' s' → Same s s' → Q s') : WP isa (.block is) s Q := by
  induction is generalizing ρ s with
  | nil => cases hs; exact WP.block_nil (hQ s hr ⟨s.xmm, rfl⟩)
  | cons i is ih =>
    unfold run at hs
    split at hs <;> [rename_i σ hσ; cases hs]
    obtain ⟨d, v, he, hr'⟩ := step_ok hr hσ
    exact Wp.cons he (ih hr' hs fun s' h₁ h₂ => hQ s' h₁ (Same.trans ⟨_, rfl⟩ h₂))

/-! ## The entry state -/

/-- Register `k`. -/
def xreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

/-- The input bytes of a state: byte `i` of register `k` is input byte
`16 k + i`, and byte `o` of the keys `128 + o`. -/
def envOf (p : Params) (s : State) (n : Nat) : BitVec 8 :=
  if n < 128 then byte (s.xmm (xreg (n / 16))) (n % 16)
  else s.mem ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 (n - 128))

theorem envOf_reg (p : Params) (s : State) (r : XReg) {i : Nat} (hi : i < 16) :
    envOf p s (16 * r.ctorIdx + i) = byte (s.xmm r) i := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [envOf, ite_eq_left (by omega_using [hr, hi]), show (16 * r.ctorIdx + i) / 16 = r.ctorIdx by omega_arith,
    show (16 * r.ctorIdx + i) % 16 = i by omega_arith]
  cases r <;> rfl

theorem envOf_key (p : Params) (s : State) (o : Nat) :
    envOf p s (128 + o) = s.mem ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 o) := by
  rw [envOf, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]

theorem init_get (r : XReg) : Regs.init.get r = ⟨false, bytes fun i => .var (16 * r.ctorIdx + i)⟩ := by
  cases r <;> rfl

/-- A state whose table register holds the table's address and whose keys
are readable is what the registers on entry describe. -/
theorem rel_init (htb : s.gpr p.tb = s.syms p.name) (hfit : (s.gpr p.kreg).toNat + p.klen ≤ 2 ^ 32)
    (hacc : ∀ o, o + 16 ≤ p.klen → InRegions (s.rd ++ s.wr) (addr (s.gpr p.kreg) o) 16) :
    Rel p (envOf p s) Regs.init s := by
  refine ⟨htb, fun o i ho hi => ?_, hacc, fun r => ?_⟩
  · rw [show 128 + o + i = 128 + (o + i) by omega_arith, envOf_key, addr_eq (by omega_using [hfit, ho]),
      BitVec.add_assoc]
    exact congrArg (fun a => s.mem ((s.gpr p.kreg).setWidth 64 + a)) (by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using [hfit, ho, hi])
  · rw [init_get, holds_plain]
    intro i hi
    have hr : r.ctorIdx < 8 := by cases r <;> decide
    rw [get_bytes _ hi, BV.var_eval _ (by show 16 * r.ctorIdx + i < 1024; omega_using [hr, hi]), envOf_reg p s r hi]

/-- A register known to hold constants. -/
theorem Rel.const (hr : Rel p env ρ s) (r : XReg) {c : Nat → BitVec 8} (h : ∀ i < 16, byte (s.xmm r) i = c i) :
    Rel p env (ρ.set r ⟨false, bytes fun i => .cst (c i)⟩) s := by
  refine ⟨hr.tb, hr.key, hr.acc, fun r' => ?_⟩
  rw [Regs.get_set]
  by_cases e : r' = r
  · rw [ite_eq_left e, e, holds_plain]
    intro i hi
    rw [get_bytes _ hi, BV.cst_eval, h i hi]
  · rw [ite_eq_right e]; exact hr.regs r'

/-- The bytes of a register the expressions leave plain. -/
theorem Rel.bytes (hr : Rel p env ρ s) {r : XReg} (h : (ρ.get r).sh = false) :
    ∀ i < 16, byte (s.xmm r) i = (get (ρ.get r).bs i).eval env := by
  have := hr.regs r
  rw [Holds, ite_eq_right (by rw [h]; exact Bool.false_ne_true)] at this
  exact this

end

/-! ## Stores -/

/-- The stores of a block: the offset in the output region, and the 16
bytes stored there. -/
abbrev Outs := List (Nat × List BV)

/-- The output region: its base register and its length. -/
structure OParams where
  oreg : Reg
  olen : Nat

/-- `step`, or a store of a plain register to the output region, apart from
the stores before it. -/
def stepS (p : Params) (q : OParams) (σ : Regs × Outs) : Instr → Option (Regs × Outs)
  | .movdquStore m r =>
    if m.base = q.oreg ∧ m.disp + 16 ≤ q.olen ∧
        σ.2.all (fun e => decide (e.1 + 16 ≤ m.disp ∨ m.disp + 16 ≤ e.1)) = true then
      (plain σ.1 r).map fun bs => (σ.1, (m.disp, bs) :: σ.2)
    else none
  | i => (step p σ.1 i).map fun ρ => (ρ, σ.2)

def runS (p : Params) (q : OParams) : Regs × Outs → List Instr → Option (Regs × Outs)
  | σ, [] => some σ
  | σ, i :: is =>
    match stepS p q σ i with
    | some σ' => runS p q σ' is
    | none => none

/-- The bytes stored at offset `o`. -/
def outAt : Outs → Nat → Option (List BV)
  | [], _ => none
  | (o', bs) :: l, o => if o' = o then some bs else outAt l o

theorem outAt_mem : ∀ {l : Outs} {o : Nat} {bs : List BV}, outAt l o = some bs → (o, bs) ∈ l
  | [], _, _, h => by cases h
  | (o', bs') :: l, o, bs, h => by
    unfold outAt at h
    by_cases e : o' = o
    · rw [ite_eq_left e] at h; cases h; rw [e]; exact List.mem_cons_self
    · rw [ite_eq_right e] at h; exact List.mem_cons_of_mem _ (outAt_mem h)

/-- The bytes stored at offset `o` are `f`'s, up to the order of the terms. -/
def outOk (l : Outs) (o : Nat) (f : Nat → BV) : Bool :=
  match outAt l o with
  | some bs => (List.range 16).all fun i => (get bs i).same (f i)
  | none => false

/-- What the stores need of the state the block starts in: the output
region is writable, apart from the keys, and neither wraps around. -/
structure OutOk (p : Params) (q : OParams) (s₀ : State) : Prop where
  fit : (s₀.gpr q.oreg).toNat + q.olen ≤ 2 ^ 32
  wr : ∀ o, o + 16 ≤ q.olen → InRegions s₀.wr (addr (s₀.gpr q.oreg) o) 16
  sep : Region.Disjoint ⟨(s₀.gpr p.kreg).setWidth 64, p.klen⟩ ⟨(s₀.gpr q.oreg).setWidth 64, q.olen⟩
  kfit : (s₀.gpr p.kreg).toNat + p.klen ≤ 2 ^ 32

/-- The state the expressions and stores `σ` describe, from the state `s₀`
the block starts in: `Rel`, the registers other than the XMM registers and
the regions as they were, memory as it was outside the 16 bytes of each
store, and in them what was stored. -/
structure RelS (p : Params) (q : OParams) (env : Nat → BitVec 8) (σ : Regs × Outs) (s₀ s : State) : Prop where
  rel : Rel p env σ.1 s
  gpr : s.gpr = s₀.gpr
  zf : s.zf = s₀.zf
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  frame : Frame (σ.2.map fun e => ⟨(s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 e.1, 16⟩) s₀.mem s.mem
  outs : ∀ e ∈ σ.2, e.1 + 16 ≤ q.olen ∧ ∀ i < 16,
    s.mem ((s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 (e.1 + i)) = (get e.2 i).eval env

section
variable {p : Params} {q : OParams} {env : Nat → BitVec 8} {σ : Regs × Outs} {s₀ s : State}

theorem RelS.init (h : Rel p env σ.1 s) (ho : σ.2 = []) : RelS p q env σ s s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun e he => by rw [ho] at he; cases he⟩

/-- The offsets of the stores are within `[lo, hi)`. -/
def outsIn (l : Outs) (lo hi : Nat) : Bool := l.all fun e => decide (lo ≤ e.1 ∧ e.1 + 16 ≤ hi)

/-- Memory is as it was outside the bytes `[lo, hi)` of the output region,
which hold every store. -/
theorem RelS.frameIn (hr : RelS p q env σ s₀ s) {lo hi : Nat} (h : outsIn σ.2 lo hi = true) :
    Frame [⟨(s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 lo, hi - lo⟩] s₀.mem s.mem :=
  hr.frame.sub fun r hr' => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    have := of_decide_eq_true (List.all_eq_true.mp h e he)
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ this.1 (by omega_using [this])⟩

/-- What was stored at offset `o`. -/
theorem RelS.out (hr : RelS p q env σ s₀ s) {o : Nat} {f : Nat → BV} (h : outOk σ.2 o f = true) {i : Nat}
    (hi : i < 16) : s.mem ((s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 (o + i)) = (f i).eval env := by
  unfold outOk at h
  split at h <;> [rename_i bs hb; cases h]
  rw [← BV.same_eval env (List.all_eq_true.mp h i (List.mem_range.mpr hi))]
  exact (hr.outs _ (outAt_mem hb)).2 i hi

theorem stepS_ok (ok : OutOk p q s₀) {i : Instr} {σ' : Regs × Outs} (hr : RelS p q env σ s₀ s)
    (hs : stepS p q σ i = some σ') : ∃ s', exec i s = some s' ∧ RelS p q env σ' s₀ s' := by
  unfold stepS at hs
  split at hs
  · rename_i m r
    split at hs <;> [rename_i hc; cases hs]
    obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hbase, hlen, hall⟩ := hc
    have hfit := ok.fit
    have ha : addr (s₀.gpr q.oreg) m.disp = (s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 m.disp :=
      addr_eq (by omega_using [hfit, hlen])
    have hea : s.ea m = (s₀.gpr q.oreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
      show addr (s.gpr m.base) m.disp = _
      rw [hbase, hr.gpr, ha]
    have hf : Frame [⟨(s₀.gpr q.oreg).setWidth 64, q.olen⟩] s.mem (s.mem.writeW (s.ea m) (s.xmm r)) := by
      rw [hea]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show m.disp + 128 / 8 ≤ q.olen by omega_using [hlen]) (by omega_using [hfit, hlen]))
    refine ⟨{ s with mem := s.mem.writeW (s.ea m) (s.xmm r) }, ?_, ⟨hr.rel.tb, fun o i ho hi => ?_, hr.rel.acc,
      hr.rel.regs⟩, hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, ?_, fun e he => ?_⟩
    · show s.store128 (s.ea m) (s.xmm r) = _
      rw [State.store128, ite_eq_left (by rw [hea, ← ha, hr.wr]; exact ok.wr _ hlen)]
    · show (s.mem.writeW (s.ea m) (s.xmm r)) (addr (s.gpr p.kreg) o + BitVec.ofNat 64 i) = _
      rw [← hr.rel.key o i ho hi]
      refine hf _ fun R hR hc => ?_
      rw [List.mem_singleton] at hR; subst hR
      refine ok.sep _ ?_ hc
      have hk := ok.kfit
      rw [hr.gpr, addr_eq (by omega_using [hk, ho]), Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_using [ho, hi]) (by omega_using [hk, ho, hi])
    · show Frame (_ :: _) s₀.mem (s.mem.writeW (s.ea m) (s.xmm r))
      rw [hea]
      exact (hr.frame.mono fun r hr => List.mem_cons_of_mem _ hr).writeW List.mem_cons_self _
        (Region.contains_self _ 16)
    · rcases List.mem_cons.mp he with rfl | he
      · refine ⟨hlen, fun i hi => ?_⟩
        show (s.mem.writeW (s.ea m) (s.xmm r)) _ = _
        rw [← Offset.add_ofNat_add_ofNat, ← hea,
          ← byte_readW (s.mem.writeW (s.ea m) (s.xmm r)) (s.ea m) (w := 128) (k := i) (by omega_using [hi]),
          Mem.readW_writeW_self _ _ 16 _ (by decide)]
        exact hr.rel.plain hb i hi
      · obtain ⟨hb', ho⟩ := hr.outs e he
        refine ⟨hb', fun i hi => ?_⟩
        show (s.mem.writeW (s.ea m) (s.xmm r)) _ = _
        rw [← ho i hi]
        have hd := of_decide_eq_true (List.all_eq_true.mp hall e he)
        refine Mem.write_apply ?_
        rw [hea]
        exact Offset.sep _ (d := e.1 + i) (n := 1) (e := m.disp) (k := 16) (by omega_using [hd, hi])
          (by omega_using [hfit, hb', hi]) (by omega_using [hfit, hlen]) _ (by rw [BitVec.sub_self]; decide)
  · obtain ⟨ρ, hρ, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨d, v, he, hr'⟩ := step_ok hr.rel hρ
    exact ⟨_, he, hr', hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, hr.frame, hr.outs⟩

/-- Code `runS` follows runs, and leaves what the expressions and the
stores say. -/
theorem runS_wp (ok : OutOk p q s₀) {is : List Instr} {σ' : Regs × Outs} (hr : RelS p q env σ s₀ s)
    (hs : runS p q σ is = some σ') {Q : State → Prop} (hQ : ∀ s', RelS p q env σ' s₀ s' → Q s') :
    WP isa (.block is) s Q := by
  induction is generalizing σ s with
  | nil => cases hs; exact WP.block_nil (hQ s hr)
  | cons i is ih =>
    unfold runS at hs
    split at hs <;> [rename_i τ hτ; cases hs]
    obtain ⟨s', he, hr'⟩ := stepS_ok ok hr hτ
    exact Wp.cons he (ih hr' hs)

end

end VG.X86.ByteMap
