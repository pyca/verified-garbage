module

public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Impl.X25519.X86
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on x86 (32-bit)

`vg_<curve>_{mul,add,sub}_mod_<p|n>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
cdecl: the arguments at `[esp + 4]` to `[esp + 16]`) for a modulus `m` of `k`
64-bit words (`N = 2k` 32-bit words), on the working space `ws`. The
functions use the `64 k` bytes below byte 4096 of `ws` for themselves
(`own k`): the accumulator (`2N + 1` words), the temporary area (`N` words,
`tmpAt`) and the saved registers (`saveAt`). The
modulus is in the code (immediates), so it is not stored.

* `mulFn`: Montgomery's product: `ebx`, `esi`,
  `edi` and `ebp` are saved in the own working space, `ebp` holds `ws`,
  `esi` points to `[b]` and `edi` to `[a]`. Modulo P-256's `p`, P-521's, and
  moduli of three words, it is coarsely integrated operand scanning, as
  `Impl/Mont/X86.lean`'s `mul`, but with its rows unrolled: row `i` adds
  `a_i [b]` (`mulRowB`) and `q m` (`redRowI`: P-256's
  sparse reduction for its `p`; for P-521's `p = 2⁵²¹ - 1`, whose `q` is the
  low word, that word cleared and `2⁹ q` added at word 16, `p521Red`; else a
  row of the modulus's words as immediates) to the accumulator's words from
  `i`, whose low word becomes zero. Modulo any other, it is by columns
  (`colsMul`), and a square, at equal public operand pointers, has its own
  (`colsSquare`). The accumulator's words from `N` are
  then below `2m`, reduced by a conditional subtraction (`diffsI`, `maskTop`,
  `selectsP`) into `[o]`, through `ecx`. `esi` and `edi` are restored
  before the result is stored, `ebx` and `ebp` after. For P-256 field
  squaring, equal public operand
  pointers select a full-width Comba square (36 word products) followed by
  eight sparse REDC rounds; the common final subtraction is unchanged.
  For P-521's, they select `p521Square` (153 word products, then the
  reduction as two rows by `2⁹`).
* `addFn`, `subFn`: `[a] ± [b]` into the accumulator through pointers in
  `ecx` and `edx` (`chainP`), then a conditional subtraction (the sum) or
  addition of `m` under the mask of the borrow (the difference) into
  `[o]`. Only `eax`, `ecx`, `edx` and `ebp` are written; `ebp` is saved in
  the own working space.

The functions never write `esi` or `edi` but to restore them before any
store at an address that depends on an offset (`o`): every other store is at
`ws` plus a constant. So a constant-time analysis of a caller, which analyses
the callee's code at each call, still knows the caller's `esi` and `edi`
(its loop counter and its working space) to be public after a call (the
callee's stores at computed addresses make it forget what it knew of memory).

Every address is `ws`, `ws` plus an offset or `esp`, plus a constant: only the
pointer and the offsets may affect timing.

`callOp` is a call of such a function from code whose working space is at
`edi`, with constant offsets: the arguments pushed (in a frame that `pop eax`
releases), last to first.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.Mont

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The start of the own working space: the accumulator, `2N + 1` words. -/
def own (k : Nat) : Nat := Impl.Weierstrass.Mont.ownAt k

/-- The temporary area, `N` words. -/
def tmpAt (k : Nat) : Nat := own k + (16 * k + 4)

/-- The saved `ebx`, `esi`, `edi` and `ebp`. -/
def saveAt (k : Nat) : Nat := tmpAt k + 8 * k

/-- The modulus `m` of `k` words, as `Impl/Mont/X86.lean`'s operations have
it (its words are not in memory: `mo` is unused). -/
def mod (k m : Nat) : Mod :=
  { n := k, mo := 0, tmp := tmpAt k, minv := BitVec.ofNat 64 (minv m), red := p256RedChoice k m }

/-- 32-bit word `j` of `m`. -/
def mw (m j : Nat) : BitVec 32 := BitVec.ofNat 32 (m >>> (32 * j))

/-- `[ebp + d]`. -/
def bp (d : Nat) : MemOp := at_ .ebp d

/-! ## The product -/

/-- A step of a row: `[ebp + acc + 4j] += ecx · y + ebx` for the word `y` at
`ys`, its carry word to `ebx` (it never overflows). -/
def stepG (ys : Src) (acc j : Nat) : List Instr :=
  [.mov .eax ys, .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (bp (acc + 4 * j))), .alu .adc .edx (.imm 0),
    .store (bp (acc + 4 * j)) .eax, .mov .ebx (.reg .edx)]

/-- The first step of a row, with no carry in. -/
def step0G (ys : Src) (acc : Nat) : List Instr :=
  [.mov .eax ys, .mul .ecx, .alu .add .eax (.mem (bp acc)), .alu .adc .edx (.imm 0),
    .store (bp acc) .eax, .mov .ebx (.reg .edx)]

/-- Steps `1 … r` of a row whose words `y_j` are at `ys j`. -/
def stepsG (ys : Nat → Src) (acc : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => stepsG ys acc r ++ stepG (ys (r + 1)) acc (r + 1)

/-- The carry word `ebx` added to word `N` of the window, whose word `N + 1`
becomes the carry out (its old value unread). -/
def carryUp1 (acc N : Nat) : List Instr :=
  [.mov .eax (.mem (bp (acc + 4 * N))), .alu .add .eax (.reg .ebx), .store (bp (acc + 4 * N)) .eax,
    .mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (bp (acc + 4 * N + 4)) .eax]

/-- The window at `[ebp + acc]` `+= ecx · Y`, `N` words of `Y` at `ys`, with
its carry into words `N` and `N + 1` (`carry`: `carryUp`, or `carryUp1` if
word `N + 1` is not yet written). -/
def rowG (ys : Nat → Src) (acc N : Nat) (carry : List Instr) : List Instr :=
  step0G (ys 0) acc ++ stepsG ys acc (N - 1) ++ carry

/-- Row 0's steps: `[ebp + acc + 4j] = ecx · [esi + 4j] + ebx` (the window
not yet written), its carry word to `ebx`. -/
def stepZ (acc j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * j))), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .store (bp (acc + 4 * j)) .eax, .mov .ebx (.reg .edx)]

/-- Steps `1 … r` of row 0. -/
def stepsZ (acc : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => stepsZ acc r ++ stepZ acc (r + 1)

/-- Row 0's product: the window at `[ebp + acc]` `= ecx · [esi]`, `N + 2`
words (the top one zero). -/
def rowZ (acc N : Nat) : List Instr :=
  ([.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .store (bp acc) .eax, .mov .ebx (.reg .edx)] : List Instr) ++
    stepsZ acc (N - 1) ++
    ([.store (bp (acc + 4 * N)) .ebx, .mov .eax (.imm 0), .store (bp (acc + 4 * N + 4)) .eax] : List Instr)

/-- `[esi + 4j]`. -/
def bWord (j : Nat) : Src := .mem (at_ .esi (4 * j))

/-- `m_j`. -/
def mWord (m j : Nat) : Src := .imm (mw m j)

/-- P-521's field modulus. -/
def p521Prime : Nat := 2 ^ 521 - 1

/-- P-521's field, on its eighteen 32-bit words. -/
def p521RedEnabled (M : Mod) (m : Nat) : Bool := M.n == 9 && m == p521Prime

/-- `edx:ecx = 2^9 ecx`, through `eax`. -/
def shift9 : List Instr := [.mov .eax (.reg .ecx), .mov .edx (.imm 512), .mul .edx, .mov .ecx (.reg .eax)]

/-- `T + q p` for `p = 2^521 - 1` and `q` (in `ecx`) the low word of the
window `T` at `[ebp + acc]`, of twenty words: the low word cleared (minus
`q`), and `q 2^9` added at word 16 (`2^521 = 2^9 2^512`), its low word and
then its high word (`shift9`), the carry through words 18 and 19. -/
def p521Red (acc : Nat) : List Instr :=
  ([.mov .eax (.imm 0), .store (bp acc) .eax] : List Instr) ++ shift9 ++
    sparseStep acc 16 .add true ++ ([.mov .ecx (.reg .edx)] : List Instr) ++
    sparseStep acc 17 .adc true ++ sparseStep acc 18 .adc false ++ sparseStep acc 19 .adc false

/-- The window `+= q m`, `q` in `ecx`: P-256's sparse identity when certified,
P-521's shift, else a row of the modulus's words. -/
def redRowI (M : Mod) (m acc : Nat) : List Instr :=
  if p256RedEnabled M then p256Red acc
  else if p521RedEnabled M m then p521Red acc
  else rowG (mWord m) acc (words M) (carryUp acc (words M))

/-- Row `i`: `ecx = a_i` (through `edi`), the window at `own + 4i`
`+= a_i [b]` (row 0 writes it), then `+= q m` for `q = t₀ m' mod 2³²`. -/
def rowF (k m i : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .edi (4 * i)))] ++
    (if i = 0 then rowZ (own k) (2 * k)
      else rowG bWord (own k + 4 * i) (2 * k) (carryUp1 (own k + 4 * i) (2 * k))) ++
    redDigit (mod k m) (own k + 4 * i) ++ redRowI (mod k m) m (own k + 4 * i)

/-- The rows `0 … r - 1`. -/
def rowsF (k m : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => rowsF k m r ++ rowF k m r

/-! ## The conditional subtraction, and the result -/

/-- `[ebp + tmp] = [ebp + src] - m`, `N` words, with its borrow, through `eax`. -/
def diffsI (m src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .eax (.mem (bp (src + 4 * j))), .alu (if j = 0 then .sub else .sbb) .eax (.imm (mw m j)),
      .store (bp (tmp + 4 * j)) .eax]

/-- The mask `eax`: all ones if the number at `[ebp + src]` (`N` words and the
top word) is at least `m` (the top word does not borrow). -/
def maskTop (src N : Nat) : List Instr :=
  [.mov .eax (.mem (bp (src + 4 * N))), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax),
    .alu .xor .eax (.imm (-1))]

/-- `ecx = ws + o`. -/
def outPtr : List Instr := [.mov .ecx (.mem (at_ .esp 8)), .alu .add .ecx (.reg .ebp)]

/-- `[ecx] = [ebp + tmp]` where the mask `eax` is all ones, else `[ebp + src]`,
`N` words, through `edx`. -/
def selectsP (src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.mem (bp (src + 4 * j))), .alu .xor .edx (.mem (bp (tmp + 4 * j))), .alu .and .edx (.reg .eax),
      .alu .xor .edx (.mem (bp (src + 4 * j))), .store (at_ .ecx (4 * j)) .edx]

/-- The number below `2m` at `[ebp + src]` reduced modulo `m` into `[ecx]`
(`ecx = ws + o`, formed after the mask), with `rest` (restoring registers
that the stores through `ecx` must not lose) before the stores. -/
def csubOut (k m src : Nat) (rest : List Instr) : List Instr :=
  diffsI m src (tmpAt k) (2 * k) ++ maskTop src (2 * k) ++ outPtr ++ rest ++ selectsP src (tmpAt k) (2 * k)

/-! ## The functions -/

/-- `vg_<curve>_mul_mod_<p|n>`'s entry: `ebx`, `esi`, `edi` and `ebp` saved,
`ebp = ws`, `esi = ws + b`, `edi = ws + a`. -/
def mulEntry (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax (saveAt k)) .ebx, .store (at_ .eax (saveAt k + 4)) .esi,
    .store (at_ .eax (saveAt k + 8)) .edi, .store (at_ .eax (saveAt k + 12)) .ebp,
    .mov .ebp (.reg .eax),
    .mov .esi (.mem (at_ .esp 16)), .alu .add .esi (.reg .ebp),
    .mov .edi (.mem (at_ .esp 12)), .alu .add .edi (.reg .ebp)]

/-- `esi` and `edi` restored. -/
def mulRestoreSI (k : Nat) : List Instr :=
  [.mov .esi (.mem (bp (saveAt k + 4))), .mov .edi (.mem (bp (saveAt k + 8)))]

/-- `ebx` and `ebp` restored (`ebp` last). -/
def restoreBP (k : Nat) : List Instr :=
  [.mov .ebx (.mem (bp (saveAt k))), .mov .ebp (.mem (bp (saveAt k + 12)))]

/-- Sparse reduction of an already populated product. Unlike CIOS, carry
and borrow propagate through every remaining high word. -/
def squareRed (acc extra : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (bp acc) .eax] ++
  multiChain (acc + 12) positiveMask (7 + extra) ++
  sparseChain (acc + 28) .sub .sbb (3 + extra)

/-- One full-product REDC round, including its reduction digit. -/
def squareRound (i : Nat) : List Instr :=
  [.mov .ecx (.mem (bp (own 4 + 4 * i)))] ++ squareRed (own 4 + 4 * i) (7 - i)

/-- The first `r` reduction rounds. -/
def squareRounds : Nat → List Instr
  | 0 => []
  | r + 1 => squareRounds r ++ squareRound r

/-- Words `0 … j - 1` of the operand at `[r]` copied to `[ebp + d]`, before
Comba uses the general-purpose registers for its accumulator. -/
def copyWords (r : Reg) (d : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => copyWords r d j ++ [.mov .eax (.mem (at_ r (4 * j))), .store (bp (d + 4 * j)) .eax]

/-- The sixteen Comba columns, before modular reduction. -/
def squareProduct : List Instr :=
  VG.Impl.X25519.X86.zeroAcc ++
    VG.Impl.X25519.X86.cols (own 4) 16 (VG.Impl.X25519.X86.sqrTerms (tmpAt 4))

/-- Restore the Montgomery base after the Comba accumulator used `ebp`. -/
def squareProductBase : List Instr := squareProduct ++ [.mov .ebp (.reg .edi)]

/-- Copy, square, and initialize the extra high word for REDC. -/
def squareInit : List Instr :=
  copyWords .esi (tmpAt 4) 8 ++ [.mov .edi (.reg .ebp)] ++ squareProductBase ++
    [.store (bp (own 4 + 64)) .ebx]

/-- The square before the common final conditional subtraction. -/
def squareBody : List Instr := squareInit ++ squareRounds 8


/-! ## P-521's square

`[a]²` for `[a]` below `p = 2⁵²¹ - 1`, whose top word is zero, in the
accumulator's 37 words, by the rows' own steps: the products of different
words (`sqRows`: row `i` adds `a_i (a_0 … a_{i-1})` at word `i`), doubled
(`dblWords`), and the squares `a_i²` at words `2i` and `2i + 1`
(`diagSteps`), 153 products; then `(P + L p) / 2⁵⁷⁶` as two rows by `2⁹`
(`p521Fold`, as `2⁵²¹ = 2⁹ 2⁵¹²`): the low sixteen words `L₀` added at word
16, which clears them, then the next two at word 32. -/

/-- Words `0 … n - 1` of the number at `[ebp + acc]` cleared. -/
def zeroWords (acc n : Nat) : List Instr :=
  .mov .eax (.imm 0) :: (List.range n).map fun j => .store (bp (acc + 4 * j)) .eax

/-- `[ebp + d + 4j]`. -/
def accWord (d j : Nat) : Src := .mem (bp (d + 4 * j))

/-- Row `i` of the products of different words: `ecx = a_i` (through
`esi`), and the window at word `i` `+= a_i (a_0 … a_{i-1})`. -/
def sqRow (acc i : Nat) : List Instr :=
  ([.mov .ecx (.mem (at_ .esi (4 * i)))] : List Instr) ++
    rowG bWord (acc + 4 * i) i (carryUp (acc + 4 * i) i)

/-- The rows `1 … r`. -/
def sqRows (acc : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => sqRows acc r ++ sqRow acc (r + 1)

/-- Words `0 … n - 1` doubled in place: a row's steps by `ecx = 1` of the
words themselves, the carry word in `ebx`. -/
def dblSteps (acc : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => dblSteps acc n ++ stepG (accWord acc n) acc n

/-- The `n` words at `[ebp + acc]` doubled. -/
def dblWords (acc n : Nat) : List Instr :=
  ([.mov .ecx (.imm 1), .mov .ebx (.imm 0)] : List Instr) ++ dblSteps acc n

/-- `a_i²` added at words `2i` and `2i + 1`, with the carry word `ebx`. -/
def diagStep (acc i : Nat) : List Instr :=
  ([.mov .ecx (.mem (at_ .esi (4 * i)))] : List Instr) ++ stepG (bWord i) acc (2 * i) ++
    stepG (.imm 0) acc (2 * i + 1)

/-- The squares of words `0 … n - 1`. -/
def diagSteps (acc : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => diagSteps acc n ++ diagStep acc n

/-- `(P + L p) / 2⁵⁷⁶` for the product `P` at `[ebp + acc]`, in words `18 … 35`:
words `16 … 33` `+= 2⁹` (words `0 … 15`), then words `32 … 35` `+= 2⁹`
(words `16`, `17`). -/
def p521Fold (acc : Nat) : List Instr :=
  ([.mov .ecx (.imm 512)] : List Instr) ++
    rowG (accWord acc) (acc + 64) 16 (carryUp (acc + 64) 16) ++
    rowG (accWord (acc + 64)) (acc + 128) 2 (carryUp (acc + 128) 2)

/-- P-521's square before the common final conditional subtraction. -/
def p521Square : List Instr :=
  zeroWords (own 9) 37 ++ sqRows (own 9) 16 ++ dblWords (own 9) 34 ++
    ([.mov .ebx (.imm 0)] : List Instr) ++ diagSteps (own 9) 17 ++ p521Fold (own 9)

/-! ## Any other modulus's product, by columns

The product of `N` words `[a] [b]` and its Montgomery reduction together, a
column at a time, in the accumulator `ebx:ecx:ebp` (Comba's method): `edi`
holds `ws`, and the operands are copied below it first (a square, at equal
pointers, copies one, and adds the products of different words once,
doubled). Column `c < N` adds the products `a_i b_{c-i}` and
`q_i m_{c-i}`, and then `q_c m_0` for its digit `q_c`, which clears the
column's low word. The columns from `N` are the result's words, which
overwrite the digits as they are no longer needed. Products by a zero word
of `m` are left out. -/

/-- Column `c` of `[A] [B]`, `N` words each. -/
def mulTerms (A B N c : Nat) : List Impl.X25519.X86.Term :=
  (List.range (c + 1)).filterMap fun i =>
    if i < N ∧ c - i < N then some (.mulM (A + 4 * i) (B + 4 * (c - i))) else none

/-- Column `c` of `[A]²`, `N` words. -/
def sqTerms (A N c : Nat) : List Impl.X25519.X86.Term :=
  (List.range (c + 1)).filterMap fun i =>
    if c - i < N ∧ 2 * i ≤ c then
      some (if 2 * i = c then .mulM (A + 4 * i) (A + 4 * i) else .mulM2 (A + 4 * i) (A + 4 * (c - i)))
    else none

/-- Column `c` of `[Q] m`, `N` words each, without `q_c m_0`. -/
def redTerms (Q m N c : Nat) : List Impl.X25519.X86.Term :=
  (List.range c).filterMap fun i =>
    if i < N ∧ c - i < N ∧ mw m (c - i) ≠ 0 then some (.mulI (Q + 4 * i) (mw m (c - i))) else none

/-- The digit `q = ebx m' mod 2³²`, stored at `[edi + o]`, and the
accumulator `+= q m_0`, whose low word becomes zero, shifted down a word. -/
def colDigit (k m o : Nat) : List Instr :=
  .mov .eax (.reg .ebx) ::
    ((if minv32 (mod k m) = 1 then [] else [.mov .edx (.imm (minv32 (mod k m))), .mul .edx]) ++
      .store (Impl.X25519.X86.sc o) .eax :: (Impl.X25519.X86.accMul (.imm (mw m 0)) ++
        [.mov .ebx (.reg .ecx), .mov .ecx (.reg .ebp), .mov .ebp (.imm 0)]))

/-- Columns `0 … n - 1` (below `N`), for the product's terms `ts`. -/
def lowCols (k m Q : Nat) (ts : Nat → List Impl.X25519.X86.Term) : Nat → List Instr
  | 0 => []
  | n + 1 => lowCols k m Q ts n ++ ((ts n ++ redTerms Q m (2 * k) n).flatMap Impl.X25519.X86.Term.code ++
      colDigit k m (Q + 4 * n))

/-- The columns from `N`: the result's `N` words at `[edi + Q]`, and the
carry in the accumulator. -/
def highCols (k m Q : Nat) (ts : Nat → List Impl.X25519.X86.Term) : List Instr :=
  Impl.X25519.X86.cols Q (2 * k) fun j => ts (2 * k + j) ++ redTerms Q m (2 * k) (2 * k + j)

/-- The columns of the copied operands, and the result's top word. `ebp` is
`ws` before and after. -/
def montCols (k m : Nat) (ts : Nat → List Impl.X25519.X86.Term) : List Instr :=
  .mov .edi (.reg .ebp) :: (Impl.X25519.X86.zeroAcc ++
    (lowCols k m (own k + 4 * (2 * k)) ts (2 * k) ++
      (highCols k m (own k + 4 * (2 * k)) ts ++
        [.store (Impl.X25519.X86.sc (own k + 16 * k)) .ebx, .mov .ebp (.reg .edi)])))

/-- The product by columns. -/
def colsMul (k m : Nat) : List Instr :=
  copyWords .edi (own k) (2 * k) ++ (copyWords .esi (tmpAt k) (2 * k) ++
    montCols k m (mulTerms (own k) (tmpAt k) (2 * k)))

/-- The square by columns. -/
def colsSquare (k m : Nat) : List Instr :=
  copyWords .edi (own k) (2 * k) ++ montCols k m (sqTerms (own k) (2 * k))

/-- Public operand-pointer equality selects the dedicated P-256 square, or
P-521's, or the square by columns of any other modulus of four words or more
(for fewer, the rows are as fast). -/
def mulBody (k m : Nat) : Prog isa :=
  if k = 4 ∧ m = p256Prime then
    .seq (.block [.alu .cmp .edi (.reg .esi)])
      (.ite .e (.block squareBody) (.block (rowsF k m (2 * k))))
  else if k = 9 ∧ m = p521Prime then
    .seq (.block [.alu .cmp .edi (.reg .esi)])
      (.ite .e (.block p521Square) (.block (rowsF k m (2 * k))))
  else if 4 ≤ k ∧ k ≤ 9 then
    .seq (.block [.alu .cmp .edi (.reg .esi)])
      (.ite .e (.block (colsSquare k m)) (.block (colsMul k m)))
  else .block (rowsF k m (2 * k))

/-- `vg_<curve>_mul_mod_<p|n>`. -/
def mulFn (k m : Nat) : Prog isa :=
  .seq (.block (mulEntry k)) <| .seq (mulBody k m) <|
    .block (csubOut k m (own k + 4 * (2 * k)) (mulRestoreSI k) ++ restoreBP k)

/-- The entry of `add` and `sub`: `ebp` saved, `ebp = ws`, `ecx = ws + a`,
`edx = ws + b`. -/
def asEntry (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax (saveAt k + 12)) .ebp, .mov .ebp (.reg .eax),
    .mov .ecx (.mem (at_ .esp 12)), .alu .add .ecx (.reg .ebp),
    .mov .edx (.mem (at_ .esp 16)), .alu .add .edx (.reg .ebp)]

/-- `[ebp + acc] = [ecx] op [edx]`, `N` words, with `op` on the first word and
`op'` on the others, through `eax`. -/
def chainP (op op' : AluOp) (acc N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .eax (.mem (at_ .ecx (4 * j))), .alu (if j = 0 then op else op') .eax (.mem (at_ .edx (4 * j))),
      .store (bp (acc + 4 * j)) .eax]

/-- `ebp` restored. -/
def restoreP (k : Nat) : List Instr := [.mov .ebp (.mem (bp (saveAt k + 12)))]

/-- `vg_<curve>_add_mod_<p|n>`: the sum and its carry word, then the
conditional subtraction. -/
def addFn (k m : Nat) : Prog isa :=
  .block (asEntry k ++ chainP .add .adc (own k) (2 * k) ++
    [.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (bp (own k + 4 * (2 * k))) .eax] ++
    csubOut k m (own k) [] ++ restoreP k)

/-- `[ebp + tmp] = m` masked with `eax`, `N` words, through `edx`. -/
def maskedI (m tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.imm (mw m j)), .alu .and .edx (.reg .eax), .store (bp (tmp + 4 * j)) .edx]

/-- `[ecx] = [ebp + src] + [ebp + tmp]`, `N` words, through `edx`. -/
def addOut (src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.mem (bp (src + 4 * j))), .alu (if j = 0 then .add else .adc) .edx (.mem (bp (tmp + 4 * j))),
      .store (at_ .ecx (4 * j)) .edx]

/-- `vg_<curve>_sub_mod_<p|n>`: the difference, and `m` added under the mask
of its borrow, into `[o]`. -/
def subFn (k m : Nat) : Prog isa :=
  .block (asEntry k ++ chainP .sub .sbb (own k) (2 * k) ++ [.alu .sbb .eax (.reg .eax)] ++
    maskedI m (tmpAt k) (2 * k) ++ outPtr ++ addOut (own k) (tmpAt k) (2 * k) ++ restoreP k)

/-! ## Calls of the functions -/

/-- `[o] = f([a], [b])` by a call of the function `f`, whose code is `body`,
on the working space at `edi`: its arguments `(edi, o, a, b)` pushed last to
first, in a frame that `pop eax` releases. -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 o))])
    (.frame (.push [.eax, .ecx, .edx, .edi]) (.call f body) (.pop .eax 4))

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
def mulCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "mul") (mulFn S.k S.m) o a b

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
def addCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "add") (addFn S.k S.m) o a b

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
def subCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "sub") (subFn S.k S.m) o a b

end VG.Impl.Weierstrass.X86.Mont
