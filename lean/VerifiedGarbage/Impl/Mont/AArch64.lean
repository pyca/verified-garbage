import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Mont.Mod

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on AArch64

Arithmetic modulo an odd `m < 2^(64 n)`, `n` 64-bit words (`n ≤ 6`), on
numbers below `m` held in the working space as `n` little-endian words at a
constant offset from its base, which is in `x0`. The modulus is in the
working space too, at `M.mo`; `M.minv` is `-m⁻¹ mod 2⁶⁴`. With
`R = 2^(64 n)`:

* `mul o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS): for each word `a_i` of `[a]`, the accumulator
  `t += a_i [b]`, then `t += u m` for `u = t₀ m' mod 2⁶⁴`, which makes the
  low word zero, and `t /= 2⁶⁴`. The `n + 2` accumulator words are
  registers (`acc n`); the division renames them (round `i`'s words are
  `win n i 0`, `win n i 1`, …), so it costs nothing. `[b]`'s words are
  loaded into registers once (`bRegs`, all of them for `n ≤ 4`). Each
  product row is two chains of additions (`row`), one of the products' low
  words and one of their high words; `mul`, `umulh` and the shifts leave
  the carry flag alone, so each product is computed just before it is added.
  For a modulus `m ≡ -1 (mod 2⁶⁴)` (`Red.friendly`, P-256's `p`), `u = t₀`
  and `t + t₀ m = (t - t₀) + 2⁶⁴ t₀ m'` with `m' = (m + 1) / 2⁶⁴`, so the
  words above `t₀` get `t₀ m'`, whose words of zero need nothing and powers
  of two need shifts: for `p`, one product and two shifts, in one chain.
  The accumulator stays below `2m`, and the result is reduced by `csubR`.
* `add o a b`, `sub o a b`: `[a] ± [b] mod m`, with a conditional
  subtraction (`csubR`) or addition of `m`.
* `csubR`: a number below `2m` in `n` registers and a top word (0 or 1)
  reduced below `m`: the difference with `m` is computed into the registers
  `dRegs n`, free at that point, and then selected by `csel` if it did not
  borrow.

A product is `mul` and `umulh` (or shifts), the carries are `adds`, `adcs`
and `adc` (with `x7 = 0`), every selection is a mask or a `csel` on the carry,
and every address is `x0` plus
a constant: nothing but `x0` may affect timing. The operations use the
registers `x1`–`x7`, `x16`, `x17` and `acc n` (`x8`–`x13` for `n = 4`), and
write only `[o]` (their frames allow `[M.tmp]` too).
-/

namespace VG.Impl.Mont.AArch64

open VG.AArch64 VG.Impl.Mont

/-- `t = [x0 + d]`. -/
def ld (t : Reg) (d : Nat) : Instr := .ldr .x t .x0 d

/-- `[x0 + d] = t`. -/
def st (t : Reg) (d : Nat) : Instr := .str .x t .x0 d

/-- `r = v`, by `movz` and three `movk`s. -/
def const64 (r : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x r (v.extractLsb' 0 16) 0, .movk .x r (v.extractLsb' 16 16) 1,
    .movk .x r (v.extractLsb' 32 16) 2, .movk .x r (v.extractLsb' 48 16) 3]

/-- `x7 = 0`, for the carries. -/
def zero7 : Instr := .movz .x .x7 0 0

/-- The accumulator's registers: `n + 2` of `x8`–`x15`. -/
def acc (n : Nat) : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15].take (n + 2)

/-- Word `j` of the accumulator in round `i`: the registers rotate by one
word each round. -/
def win (n i j : Nat) : Reg := (acc n).getD ((i + j) % (n + 2)) .x8

/-- The words of round `i`'s accumulator, low to high. -/
def wins (n i : Nat) : List Reg := (List.range (n + 2)).map (win n i)

/-- `ds = ts - [mo]`, word by word, with `subs` on the first word and `sbcs` on
the others, through `x2`. -/
def diffsR (first : Bool) : List Reg → List Reg → Nat → List Instr
  | t :: ts, d :: ds, mo =>
    [ld .x2 mo, if first then .subs .x d t .x2 else .sbcs .x d t .x2] ++ diffsR false ts ds (mo + 8)
  | _, _, _ => []

/-- `ts = ds` where the carry is set (the difference did not borrow), word by
word. -/
def selectsR : List Reg → List Reg → List Instr
  | t :: ts, d :: ds => .csel .x t d t :: selectsR ts ds
  | _, _ => []

/-- The registers free for the difference when a sum or product is reduced. -/
def dRegs (n : Nat) : List Reg := [.x1, .x3, .x4, .x5, .x6, .x16].take n

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`, in
registers: the difference with `m` into `dRegs n`, and selected where it did
not borrow (the carry is set). -/
def csubR (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffsR true ts (dRegs M.n) M.mo ++ [.sbcs .x .x2 top .x7] ++ selectsR ts (dRegs M.n)

/-- `[o] = ts`. -/
def stores : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => st t o :: stores ts (o + 8)

/-- `ts = [a]`. -/
def loads : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => ld t a :: loads ts (a + 8)

/-- `ts := 0`. -/
def zeros (ts : List Reg) : List Instr := ts.map fun t => .movz .x t 0 0

/-! ## Multiplication

A row adds `x · W` to words of the accumulator, for a multiplier register
`x` and a multiplicand `W` of words (`RWord`): zero, one, a power of two, or
any word (`gen`), in a register, in the working space or a constant (`Src`).
The products' low words go in one chain of additions and their high words,
one word up, in another, except that a high word goes in the first chain
where no low word is (above a word of `W` that is zero or one): so a
multiplicand with zero words needs one chain (`pieceA`, `pieceB`). A
power of two needs shifts, not products, and one needs nothing. `mul`, `umulh`
and the shifts leave the carry flag alone, so each piece is computed into
`x2` just before its addition. -/

/-- Where a word of a multiplicand is: a register, a word of the working
space, or a constant. -/
inductive Src
  | reg (r : Reg)
  | mem (d : Nat)
  | imm (v : BitVec 64)

/-- The source's word into `x3`, unless it is a register. -/
def Src.fetch : Src → List Instr
  | .reg _ => []
  | .mem d => [ld .x3 d]
  | .imm v => const64 .x3 v

/-- The register holding the source's word once fetched. -/
def Src.out : Src → Reg
  | .reg r => r
  | _ => .x3

/-- A word of a multiplicand. -/
inductive RWord
  | zero
  | one
  | pow2 (k : Nat)
  | gen (s : Src)

/-- A word of the row `x · W`: the low or high word of `x w`, `x 2^k mod 2⁶⁴`,
`⌊x / 2^k⌋`, or `x`. -/
inductive Piece
  | lo (s : Src)
  | hi (s : Src)
  | shl (k : Nat)
  | shr (k : Nat)
  | self

/-- The piece of the multiplier `x` into `x2` (`self` is `x` itself). -/
def Piece.code (x : Reg) : Piece → List Instr
  | .lo s => s.fetch ++ [.mul .x .x2 x s.out]
  | .hi s => s.fetch ++ [.umulh .x2 x s.out]
  | .shl k => [.lsl .x .x2 x k]
  | .shr k => [.lsr .x .x2 x k]
  | .self => []

/-- The register holding the piece. -/
def Piece.reg (x : Reg) : Piece → Reg
  | .self => x
  | _ => .x2

/-- The low word of `x w` as a piece, if it may be nonzero. -/
def RWord.lo : RWord → Option Piece
  | .zero => none
  | .one => some .self
  | .pow2 k => some (.shl k)
  | .gen s => some (.lo s)

/-- The high word of `x w` as a piece, if it may be nonzero. -/
def RWord.hi : RWord → Option Piece
  | .zero => none
  | .one => none
  | .pow2 k => some (.shr (64 - k))
  | .gen s => some (.hi s)

/-- The first chain's piece at word `j` of the row: the low word of `x w_j`,
or else the high word of `x w_{j-1}`. -/
def pieceA (ws : List RWord) (j : Nat) : Option Piece :=
  match (ws.getD j .zero).lo with
  | some p => some p
  | none => if j = 0 then none else (ws.getD (j - 1) .zero).hi

/-- The second chain's piece at word `j`: the high word of `x w_{j-1}`, where
the first chain has the low word of `x w_j`. -/
def pieceB (ws : List RWord) (j : Nat) : Option Piece :=
  if j = 0 then none else
    match (ws.getD j .zero).lo, (ws.getD (j - 1) .zero).hi with
    | some _, some h => some h
    | _, _ => none

/-- `adds` (the first word of a chain) or `adcs`. -/
def addOp (first : Bool) (t r : Reg) : Instr := if first then .adds .x t t r else .adcs .x t t r

/-- A word of a chain: `t += ` its piece (or zero, `x7`), with the carry. -/
def stepCode (x : Reg) (first : Bool) (t : Reg) : Option Piece → List Instr
  | some p => p.code x ++ [addOp first t (p.reg x)]
  | none => [addOp first t .x7]

/-- A chain from its first word. -/
def chainCode (x : Reg) : Bool → List (Reg × Option Piece) → List Instr
  | _, [] => []
  | first, (t, o) :: rest => stepCode x first t o ++ chainCode x false rest

/-- A chain, skipping the words before its first piece. -/
def chainSkip (x : Reg) : List (Reg × Option Piece) → List Instr
  | [] => []
  | (_, none) :: rest => chainSkip x rest
  | (t, some p) :: rest => stepCode x true t (some p) ++ chainCode x false rest

/-- The pieces of a chain over the words `ts`, from word `j` of the row. -/
def pieces (f : List RWord → Nat → Option Piece) (ws : List RWord) :
    List Reg → Nat → List (Reg × Option Piece)
  | [], _ => []
  | t :: ts, j => (t, f ws j) :: pieces f ws ts (j + 1)

/-- `ts += x · W`: both chains. -/
def row (x : Reg) (ts : List Reg) (ws : List RWord) : List Instr :=
  chainSkip x (pieces pieceA ws ts 0) ++ chainSkip x (pieces pieceB ws ts 0)

/-- The registers holding the words of `[b]`, the multiplicand. -/
def bRegs : List Reg := [.x4, .x5, .x16, .x17]

/-- Word `j` of the multiplicand at `b`: a register, or a load. -/
def bSrc (b j : Nat) : Src := match bRegs[j]? with
  | some r => .reg r
  | none => .mem (b + 8 * j)

/-- The multiplicand's words `j`, …, `j + k - 1`. -/
def bWords (b : Nat) : Nat → Nat → List RWord
  | _, 0 => []
  | j, k + 1 => .gen (bSrc b j) :: bWords b (j + 1) k

/-- The modulus's words `j`, …, `j + k - 1`, in the working space at `mo`. -/
def mWords (mo : Nat) : Nat → Nat → List RWord
  | _, 0 => []
  | j, k + 1 => .gen (.mem (mo + 8 * j)) :: mWords mo (j + 1) k

/-- The first word of `m'` that is neither zero, one nor a power of two,
which `x6` holds. -/
def firstGen : List MWord → Option Nat
  | [] => none
  | .gen v :: _ => some v
  | _ :: ws => firstGen ws

/-- `m'`'s words: those equal to `firstGen` in `x6`, other values as
constants. -/
def fWord (g : Option Nat) : MWord → RWord
  | .zero => .zero
  | .one => .one
  | .pow2 k => .pow2 k
  | .gen v => if g = some v then .gen (.reg .x6) else .gen (.imm (BitVec.ofNat 64 v))

/-- `x6`: `minv`, or the first general word of `m'`. -/
def mulConst (M : Mod) : List Instr :=
  match M.red with
  | .general => const64 .x6 M.minv
  | .friendly ws => match firstGen ws with
    | some v => const64 .x6 (BitVec.ofNat 64 v)
    | none => []

/-- The first row, into the cleared accumulator `ts` (`n + 1` words) for the
multiplicand's words in the registers `bs`: the low words of `x b_j` straight
into `ts`, and then a chain of the high words, one word up. -/
def rowInit (x : Reg) (ts bs : List Reg) : List Instr :=
  (ts.zip bs).map (fun (t, r) => .mul .x t x r) ++
    chainSkip x ((ts.tail.zip bs).map fun (t, r) => (t, some (.hi (.reg r))))

/-- The words a row of products adds to: the window, or its low `n + 1` words
for a tight modulus, whose sum fits in them. -/
def prodWins (M : Mod) (i : Nat) : List Reg :=
  if M.tight then (wins M.n i).take (M.n + 1) else wins M.n i

/-- `T += a_i [b]`: the first row straight into the cleared accumulator when
`[b]` is in registers, else a row. -/
def prodRow (M : Mod) (a b i : Nat) : List Instr :=
  [ld .x1 (a + 8 * i)] ++
    if i = 0 ∧ M.n ≤ 4 then rowInit .x1 ((wins M.n 0).take (M.n + 1)) (bRegs.take M.n)
    else row .x1 (prodWins M i) (bWords b 0 M.n)

/-- Round `i` of `mul o a b`: `T += a_i [b]`, then `T += u m` with
`u = t₀ m' mod 2⁶⁴`, after which `t₀ = 0`; or, for a friendly modulus,
`T = ⌊T / 2⁶⁴⌋ + t₀ m'` in the words above `t₀`, and `t₀ = 0`. -/
def round (M : Mod) (a b i : Nat) : List Instr :=
  prodRow M a b i ++
    match M.red with
    | .general => .mul .x .x1 (win M.n i 0) .x6 :: row .x1 (wins M.n i) (mWords M.mo 0 M.n)
    | .friendly ws =>
      row (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
        [.movz .x (win M.n i 0) 0 0]

/-- `x7 = 0`, the words of `[b]` in `bRegs` (all of them for `n ≤ 4`), `x6`
and the accumulator cleared. -/
def mulSetup (M : Mod) (b : Nat) : List Instr :=
  zero7 :: loads (bRegs.take M.n) b ++ mulConst M ++ zeros (acc M.n)

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (o a b : Nat) : List Instr :=
  let low := (List.range M.n).map (win M.n M.n)
  mulSetup M b ++ (List.range M.n).flatMap (round M a b) ++
    csubR M low (win M.n M.n M.n) ++ stores low o

/-- `ts op= [b]`, word by word through `x2`, with `op` on the first word and
`op'` on the others (`adds` and `adcs`, `subs` and `sbcs`). -/
def chain (op op' : Reg → Reg → Reg → Instr) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => [ld .x2 b, op t t .x2] ++ chain op' op' ts (b + 8)

/-- The low words and the top word of the sums and differences. -/
def low (n : Nat) : List Reg := (acc n).take n
def top (n : Nat) : Reg := (acc n).getD n .x8

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.adds .x) (.adcs .x) (low M.n) b ++
    [.adc .x (top M.n) .x7 .x7] ++ csubR M (low M.n) (top M.n) ++ stores (low M.n) o

/-- `ts += [mo]` masked with `x17`, word by word through `x2`. -/
def addMasked (first : Bool) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, mo => [ld .x2 mo, .logic .and .x .x2 .x2 .x17,
      if first then .adds .x t t .x2 else .adcs .x t t .x2] ++ addMasked false ts (mo + 8)

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`x17` of its borrow. -/
def sub (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.subs .x) (.sbcs .x) (low M.n) b ++
    [.sbc .x .x17 .x7 .x7] ++ addMasked true (low M.n) M.mo ++ stores (low M.n) o

end VG.Impl.Mont.AArch64
