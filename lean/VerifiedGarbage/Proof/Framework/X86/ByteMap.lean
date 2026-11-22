module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.Omega

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

The instructions followed: `movdqa`, `pxor`, `pand` with a register of
constants, `pshufb` of constants (a look-up) or by constants (a shuffle),
`aesenclast`, `psrld` by 4 (only to be masked next, the high nibbles),
`pshufd`, `punpcklqdq`, `punpckhqdq`, and the loads of a table an
instruction carries (constants), and of 16 or 8 bytes of the keys.
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
      if (byte b i).msb then 0 else byte a ((byte b i).extractLsb' 0 4).toNat := by
  show byte (ofBytes fun i => if (byte b i).msb then 0 else byte a ((byte b i).extractLsb' 0 4).toNat) i = _
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
    (plain ρ a).bind fun x => (plain ρ b).map fun y => ρ.set a ⟨false, bytes fun i => (get x i).xor (get y i)⟩
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

end VG.X86.ByteMap
