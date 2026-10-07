import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Short Weierstrass curves on x86-64: inversion by divsteps

`[acc] = [base]^(p - 2)` for a prime `p` (`InvCfg.inv`), as the inverse of
`[base]` (zero for zero) by Bernstein–Yang divsteps in batches of `N = 59`
(`Proof/Divstep/Alg.lean`'s `invRun`), then one Montgomery multiplication by
a constant: the algorithm of `Impl/Weierstrass/AArch64/Inv.lean`. Nothing
depends on the numbers but through masks and `cmov`.

* `f`, `g`: `n + 1` words each (two's complement), from `(p, x)`.
* `a`, `b`: `n` words each in `[0, p)`, from `(0, 1)`; `f ≡ x a K`,
  `g ≡ x b K` modulo `p`.
* a batch: from `d` in `rbx` and the low words of `f` and `g`, `N`
  divsteps in packed chunks (`words`) give the matrix `(u, v, q, r)` in
  `r9`–`r12`; `(f, g) := (u f + v g, q f + r g) / 2^N` exactly,
  `(a, b) := (u a + v b, q a + r b) / 2^64 mod p`.
* the end: `f = ±1`, `res = ±a ≡ x⁻¹ 2^(-5 B)`, and `acc = res C / R` for
  `C = 2^(5 B) R³ mod p`.

The shift by five in the multi-word division uses `shl`. The model has no
arithmetic right shift, so the mask of a word's sign is `0 - (x >> 63)`. The signed
products of the matrix and the numbers are unsigned products by `mul`, less
the number shifted by a word for a negative entry (`lin`), and since `and`
clears the carry flag, the masked operands of a carry chain are copied out
first (`maskCopy`). The multi-word sums are the wide Montgomery
multiplication's rows (`memRow`, `chainW`). The registers are those of
`pow` (`rbx` and the multiplication's for 4 words: `rax`, `rcx`, `rdx`,
`rbp`, `r8`–`r13`), and the batches' count in `r14`, which the callers free
(the multiplications of six words use it too).
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-! ## Packed divsteps

A batch's `59` divsteps run in chunks of `n ≤ 15` steps (`15, 15, 15, 14`),
each from the low words of `f` and `g` in `[t]` and `[t + 8]`: with
`P = [t] mod 2^15 + 2^31` and `Q = [t + 8] mod 2^15 + 2^47` (`pset`), the
rows `u P + v Q` and `q P + r Q` of the chunk's matrix, modulo `2^64`, in
`r8` and the `g` row's register, are updated as `(f, g)` would be, doubled
rather than halved (`pstepCode`). Their bits below 15 are `2^j f_j` and
`2^j g_j`'s, so step `j`'s parity is bit `j` of the `g` row, and their
bits from 31 and 47 are `u` and `v` (`q` and `r`) plus `2^14` once
`2^30 + 2^45 + 2^61` is added (`pext`). `~d` is in `rbx`. Each chunk's
matrix updates the low words by `mul` (`plow`) and multiplies the batch's
so far in `r9`–`r12` (`pcomp`).
-/

/-- Divstep `j` of a chunk: `~d` in `rbx`, the rows in `r8` and `g`, the next
`g` row into `t`. `g << (63 - j)` is `2^63` if `g` is odd and `0` if not (its
zero flag), and adding `~d` carries if `g` is odd and `d ≥ 0` (the swap):
`t` is `g`, `g + f`, or on a swap `g - f`, `f` becomes `g` on a swap and is
doubled, and `~d` becomes `~(2 - d)` on a swap and `~(d + 2)` if not. -/
def pstepCode (j : Nat) (g t : Reg) : List Instr :=
  [.mov t (.reg g), .alu .add t (.reg .r8), .mov .rdx (.reg g), .alu .sub .rdx (.reg .r8),
    .mov .rcx (.imm (-2)), .alu .sub .rcx (.reg .rbx), .mov .rbp (.reg g), .shift .shl .rbp (63 - j),
    .cmov .e t (.reg g), .alu .add .rbp (.reg .rbx), .cmov .b t (.reg .rdx), .cmov .b .r8 (.reg g),
    .cmov .b .rbx (.reg .rcx), .alu .add .r8 (.reg .r8), .alu .sub .rbx (.imm 2)]

/-- The `g` row's register before step `j`: `r13` and `rax` in turn. -/
def gReg (j : Nat) : Reg := if j % 2 = 0 then .r13 else .rax

/-- Steps `0 … n - 1`, the `g` row then moved back to `r13`. -/
def pstepsCode (n : Nat) : List Instr :=
  (List.range n).flatMap (fun j => pstepCode j (gReg j) (gReg (j + 1))) ++
    (if n % 2 = 1 then [.mov .r13 (.reg .rax)] else [])

/-- A row's start: `r = [t] mod 2^15 + c`, through `rax`. -/
def psetRow (r : Reg) (t : Nat) (c : BitVec 64) : List Instr :=
  [.mov r (.mem (sc t)), .alu .and r (.imm 0x7fff), .movImm64 .rax c, .alu .add r (.reg .rax)]

/-- The rows' start: `r8 = [t] mod 2^15 + 2^31`, `r13 = [t + 8] mod 2^15 + 2^47`. -/
def pset (t : Nat) : List Instr := psetRow .r8 t (2 ^ 31) ++ psetRow .r13 (t + 8) (2 ^ 47)

/-- What makes the rows' fields nonnegative: `2^30` below bit 31, `2^14` at bits 31 and 47. -/
def pextC : BitVec 64 := 2 ^ 30 + 2 ^ 45 + 2 ^ 61

/-- The matrix `u, v, q, r` into `r8`, `rcx`, `r13`, `rbp`, from the rows in `r8`, `r13`. -/
def pext : List Instr :=
  [.movImm64 .rcx pextC, .alu .add .r8 (.reg .rcx), .alu .add .r13 (.reg .rcx),
    .mov .rcx (.reg .r8), .shift .shr .rcx 47, .alu .sub .rcx (.imm 16384),
    .shift .shl .r8 17, .shift .shr .r8 48, .alu .sub .r8 (.imm 16384),
    .mov .rbp (.reg .r13), .shift .shr .rbp 47, .alu .sub .rbp (.imm 16384),
    .shift .shl .r13 17, .shift .shr .r13 48, .alu .sub .r13 (.imm 16384)]

/-- `rax = [d] r` (the low word of the product), through `rdx`. -/
def ldMul (d : Nat) (r : Reg) : List Instr := [.mov .rax (.mem (sc d)), .mul r]

/-- `[e] = (rax + [d]) >> n`. -/
def addShrSt (d n e : Nat) : List Instr :=
  [.alu .add .rax (.mem (sc d)), .shift .shr .rax n] ++ [.store (sc e) .rax]

/-- `[t] = (u [t] + v [t + 8]) >> n`, `[t + 8] = (q [t] + r [t + 8]) >> n`
(modulo `2^64`), through `rax`, `rdx` and `[t + 16]`. -/
def plow (n t : Nat) : List Instr :=
  ldMul t .r8 ++ [.store (sc (t + 16)) .rax] ++ ldMul (t + 8) .rcx ++ addShrSt (t + 16) n (t + 16) ++
    ldMul t .r13 ++ [.store (sc t) .rax] ++ ldMul (t + 8) .rbp ++ addShrSt t n (t + 8) ++
    [.mov .rax (.mem (sc (t + 16))), .store (sc t) .rax]

/-- The first chunk's matrix is the batch's so far. -/
def pfirst : List Instr :=
  [.mov .r9 (.reg .r8), .mov .r10 (.reg .rcx), .mov .r11 (.reg .r13), .mov .r12 (.reg .rbp)]

/-- A column `(x, y)` of the batch's matrix, times the chunk's: `x = u x + v y`
and `y = q x + r y`, through `rax`, `rdx` and `[t]`. -/
def pcol (x y : Reg) (t : Nat) : List Instr :=
  [.mov .rax (.reg .r13), .mul x, .store (sc t) .rax] ++
    [.mov .rax (.reg .r8), .mul x, .mov x (.reg .rax), .mov .rax (.reg .rcx), .mul y, .alu .add x (.reg .rax),
      .mov .rax (.reg .rbp), .mul y] ++
    [.alu .add .rax (.mem (sc t)), .mov y (.reg .rax)]

/-- The batch's matrix times the chunk's. -/
def pcomp (t : Nat) : List Instr := pcol .r9 .r11 t ++ pcol .r10 .r12 t

/-- A chunk of `n` steps, from the low words at `[t]`, `[t + 8]`: the low
words updated unless it is the last, and the matrix the batch's if it is
the first. -/
def pchunk (t n : Nat) (first last : Bool) : List Instr :=
  pset t ++ pstepsCode n ++ pext ++ (if last then [] else plow n t) ++ (if first then pfirst else pcomp (t + 16))

/-! ## Numbers of several words in the working area -/

/-- `d = 0 - (src >> 63)`, the mask of `src`'s sign, through `rax`. -/
def maskOf (d src : Reg) : List Instr :=
  [.mov d (.reg src), .shift .shr d 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg d), .mov d (.reg .rax)]

/-- `[dst] = [src] & m` (`k` words), through `r8`. -/
def maskCopy (m : Reg) (dst src : Nat) : Nat → List Instr
  | 0 => []
  | k + 1 => [.mov .r8 (.mem (sc src)), .alu .and .r8 (.reg m), .store (sc dst) .r8] ++
      maskCopy m (dst + 8) (src + 8) k

/-- `[t] = w [x] + w' [y]`, signed, modulo `2^(64 K)` (`K` is `k` or
`k + 1`): unsigned products (`memRow`, the multiplier in `rcx`), less
`2^64 [x]` for a negative `w` and `2^64 [y]` for a negative `w'`, the masked
words copied to `[U]` first; through `rax`, `rcx`, `rdx`, `rbp`, `r8`, `r13`. -/
def lin (w w' : Reg) (t x y U k K : Nat) : List Instr :=
  zeroWords K t ++
  [.mov .rcx (.reg w)] ++ memRow k t x ++ (if k < K then [.store (sc (t + 8 * k)) .rbp] else []) ++
  [.mov .rcx (.reg w')] ++ memRow k t y ++
  (if k < K then [.mov .r8 (.mem (sc (t + 8 * k))), .alu .add .r8 (.reg .rbp), .store (sc (t + 8 * k)) .r8]
    else []) ++
  maskOf .r13 w ++ maskCopy .r13 U x (K - 1) ++ chainW .sub .sbb (K - 1) (t + 8) (t + 8) U ++
  maskOf .r13 w' ++ maskCopy .r13 U y (K - 1) ++ chainW .sub .sbb (K - 1) (t + 8) (t + 8) U

/-- `r8 *= 32`, by a left shift. -/
def shl5 : List Instr := [.shift .shl .r8 5]

/-- `[d] = (rax >> 59) + 32 r8`: a word of a shift right by 59, from the
low word in `rax` and the high word in `r8`. -/
def shrTail (d : Nat) : List Instr :=
  [.shift .shr .rax 59] ++ shl5 ++ [.alu .add .rax (.reg .r8), .store (sc d) .rax]

/-- Word `i` of `[src] / 2^59`, from words `i` and `i + 1`. -/
def shrStep (dst src i : Nat) : List Instr :=
  [.mov .rax (.mem (sc (src + 8 * i))), .mov .r8 (.mem (sc (src + 8 * (i + 1))))] ++ shrTail (dst + 8 * i)

/-- `[dst] = [src] / 2^59` (arithmetic, `L` words each): the top word's
high word is its sign's mask. -/
def shr59 (dst src L : Nat) : List Instr :=
  (List.range (L - 1)).flatMap (shrStep dst src) ++
  [.mov .rdx (.mem (sc (src + 8 * (L - 1))))] ++ maskOf .r8 .rdx ++ [.mov .rax (.reg .rdx)] ++
    shrTail (dst + 8 * (L - 1))

/-- `rcx = k = t₀ m mod 2^64`, through `rax` and `rdx`. -/
def kOf (M : Mod) (t : Nat) : List Instr :=
  [.mov .rax (.mem (sc t)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)]

/-- Word `n + 1` of `[t]`: the mask of word `n`'s sign. -/
def sextTop (M : Mod) (t : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (t + 8 * M.n)))] ++ maskOf .r8 .rdx ++ [.store (sc (t + 8 * (M.n + 1))) .r8]

/-- The two words at `d` plus `rbp`, through `r8`. -/
def carry2 (d : Nat) : List Instr :=
  [.mov .r8 (.mem (sc d)), .alu .add .r8 (.reg .rbp), .store (sc d) .r8,
    .mov .r8 (.mem (sc (d + 8))), .alu .adc .r8 (.imm 0), .store (sc (d + 8)) .r8]

/-- `[U + 8 n] = 0`, through `r8`. -/
def zeroTop (U n : Nat) : List Instr := [.mov32 .r8 (.imm 0), .store (sc (U + 8 * n)) .r8]

/-- `[t + 8] += p` (`n + 1` words) if it is negative: `p` masked by its sign
copied to `[U]` (whose top word is zero). -/
def addIfNeg (M : Mod) (t U : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (t + 8 * (M.n + 1))))] ++ maskOf .r13 .rdx ++ maskCopy .r13 U M.mo M.n ++
    chainW .add .adc (M.n + 1) (t + 8) (t + 8) U

/-- `[t + 8] -= p` (`n + 1` words), `p` copied to `[U]`. -/
def subP (M : Mod) (t U : Nat) : List Instr :=
  [.mov .r13 (.imm (-1))] ++ maskCopy .r13 U M.mo M.n ++ chainW .sub .sbb (M.n + 1) (t + 8) (t + 8) U

/-- `[dst] = mred [t]` (`n` words; `[t]` of `n + 1` words, signed, with room
for one more): `[t] += k p` for `k = t₀ m mod 2^64` (`[t]` sign-extended to
`n + 2` words), then `r =` words `1 … n + 1` brought into `[0, p)`: plus `p`
if negative, less `p`, and plus `p` if that is negative, `p` (with a zero
word on top) copied to `[U]` under the mask each time. -/
def mredC (M : Mod) (dst t U : Nat) : List Instr :=
  kOf M t ++ sextTop M t ++ memRow M.n t M.mo ++ carry2 (t + 8 * M.n) ++ zeroTop U M.n ++
  addIfNeg M t U ++ subP M t U ++ addIfNeg M t U ++ copy M.n dst (t + 8)

/-! ## The updates in registers, for four words with BMI2 and ADX

The number `t = u x + v y` (signed, modulo `2^320`) in the five registers
`aRegs` (`rcx`, `rbp`, `r8`, `r13`, `r15`, low to high): `u [x]` by `mulx`
(`rowFirst`), `v [y]` added along both carry chains (`rowAcc`), then
`2^64 [x]` taken away for a negative `u` and `2^64 [y]` for a negative `v`
(`corr`), through `rax`, `rbx` and `rdx`. -/

/-- The accumulator's registers, low to high. -/
def aRegs : List Reg := [.rcx, .rbp, .r8, .r13, .r15]

/-- `aRegs = w [x]`: of `x`'s first four words, and modulo `2^320` of all five
if `five`. -/
def rowFirst (five : Bool) (w : Reg) (x : Nat) : List Instr :=
  [.mov .rdx (.reg w), .mulx .rbp .rcx (.mem (sc x)),
    .mulx .r8 .rax (.mem (sc (x + 8))), .alu .add .rbp (.reg .rax),
    .mulx .r13 .rax (.mem (sc (x + 16))), .alu .adc .r8 (.reg .rax),
    .mulx .r15 .rax (.mem (sc (x + 24))), .alu .adc .r13 (.reg .rax)] ++
  if five then [.mulx .rbx .rax (.mem (sc (x + 32))), .alu .adc .r15 (.reg .rax)]
  else [.alu .adc .r15 (.imm 0)]

/-- `aRegs += w [y]` modulo `2^320`: of `y`'s first four words, or all five
if `five`, the low halves through OF and the high halves through CF. -/
def rowAcc (five : Bool) (w : Reg) (y : Nat) : List Instr :=
  [.mov .rdx (.reg w), .alu32 .xor .rax (.reg .rax),
    .mulx .rbx .rax (.mem (sc y)), .adox .rcx (.reg .rax), .adcx .rbp (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (y + 8))), .adox .rbp (.reg .rax), .adcx .r8 (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (y + 16))), .adox .r8 (.reg .rax), .adcx .r13 (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (y + 24))), .adox .r13 (.reg .rax), .adcx .r15 (.reg .rbx)] ++
  if five then [.mulx .rbx .rax (.mem (sc (y + 32))), .adox .r15 (.reg .rax)]
  else [.mov32 .rax (.imm 0), .adox .r15 (.reg .rax)]

/-- `aRegs -= 2^64 [x]` modulo `2^320` if `w` is negative: `x`'s first four
words times `w`'s sign bit, by `mulx` (which keeps the flags, where `and`
would clear the borrow). -/
def corr (w : Reg) (x : Nat) : List Instr :=
  [.mov .rdx (.reg w), .shift .shr .rdx 63,
    .mulx .rbx .rax (.mem (sc x)), .alu .sub .rbp (.reg .rax),
    .mulx .rbx .rax (.mem (sc (x + 8))), .alu .sbb .r8 (.reg .rax),
    .mulx .rbx .rax (.mem (sc (x + 16))), .alu .sbb .r13 (.reg .rax),
    .mulx .rbx .rax (.mem (sc (x + 24))), .alu .sbb .r15 (.reg .rax)]

/-- `aRegs = u [x] + v [y]` modulo `2^320`, `u` in `w` and `v` in `w'`. -/
def linX (five : Bool) (w w' : Reg) (x y : Nat) : List Instr :=
  rowFirst five w x ++ rowAcc five w' y ++ corr w x ++ corr w' y

/-- Word `i` of `aRegs / 2^59` into `lo`, from words `i` (`lo`) and `i + 1` (`hi`). -/
def shrWord (lo hi : Reg) : List Instr :=
  [.mov .rax (.reg hi), .shift .shl .rax 5, .shift .shr lo 59, .alu .add lo (.reg .rax)]

/-- `[dst] = aRegs / 2^59` (arithmetic, five words): each word from two, the top
one's high bits the mask of its sign. -/
def shrX (dst : Nat) : List Instr :=
  shrWord .rcx .rbp ++ shrWord .rbp .r8 ++ shrWord .r8 .r13 ++ shrWord .r13 .r15 ++
  [.mov .rax (.reg .r15), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .shift .shl .rdx 5, .shift .shr .r15 59, .alu .add .r15 (.reg .rdx)] ++ stores aRegs dst

/-- `[dst] = (u f + v g) / 2^59` (five words, signed), `u` in `w` and `v` in `w'`. -/
def fHalfX (w w' : Reg) (x y dst : Nat) : List Instr := linX true w w' x y ++ shrX dst

/-- `[dst] = t / 2^64 mod p` in `[0, p)` for `t` in `aRegs` (signed), through
`w`: `t + k p` for `k = t₀ m' mod 2^64`, whose low word is zero and its sixth
word in `w` (the sign of `t` and the carries); plus `p` if negative (`p` times
the sign bit, by `mulx`), less `p` if not below. -/
def mredX (M : Mod) (dst : Nat) (w : Reg) : List Instr :=
  [.mov .rdx (.reg .rcx), .movImm64 .rax M.minv, .mulx .rbx .rdx (.reg .rax),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .mov32 w (.imm 0), .alu .sub w (.reg .rax),
    .alu32 .xor .rax (.reg .rax),
    .mulx .rbx .rax (.mem (sc M.mo)), .adox .rcx (.reg .rax), .adcx .rbp (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (M.mo + 8))), .adox .rbp (.reg .rax), .adcx .r8 (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (M.mo + 16))), .adox .r8 (.reg .rax), .adcx .r13 (.reg .rbx),
    .mulx .rbx .rax (.mem (sc (M.mo + 24))), .adox .r13 (.reg .rax), .adcx .r15 (.reg .rbx),
    .mov32 .rax (.imm 0), .adox .r15 (.reg .rax), .adcx w (.reg .rax), .adox w (.reg .rax),
    .mov .rdx (.reg w), .shift .shr .rdx 63,
    .mulx .rcx .rax (.mem (sc M.mo)), .alu .add .rbp (.reg .rax),
    .mulx .rcx .rax (.mem (sc (M.mo + 8))), .alu .adc .r8 (.reg .rax),
    .mulx .rcx .rax (.mem (sc (M.mo + 16))), .alu .adc .r13 (.reg .rax),
    .mulx .rcx .rax (.mem (sc (M.mo + 24))), .alu .adc .r15 (.reg .rax),
    .alu .adc w (.imm 0),
    .mov .rax (.reg .rbp), .alu .sub .rax (.mem (sc M.mo)), .mov .rcx (.reg .r8), .alu .sbb .rcx (.mem (sc (M.mo + 8))),
    .mov .rdx (.reg .r13), .alu .sbb .rdx (.mem (sc (M.mo + 16))),
    .mov .rbx (.reg .r15), .alu .sbb .rbx (.mem (sc (M.mo + 24))), .alu .sbb w (.imm 0),
    .cmov .ae .rbp (.reg .rax), .cmov .ae .r8 (.reg .rcx), .cmov .ae .r13 (.reg .rdx), .cmov .ae .r15 (.reg .rbx)] ++
  stores [.rbp, .r8, .r13, .r15] dst

/-- `[dst] = mred (u a + v b)` (four words), `u` in `w` and `v` in `w'`; `w` is
written. -/
def abHalfX (M : Mod) (w w' : Reg) (x y dst : Nat) : List Instr := linX false w w' x y ++ mredX M dst w

/-! ## The configuration -/

/-- Inversion's configuration: the field, the result and input slots, the
working area of `8 n + 8` words, the number of batches, and the final constant. -/
structure InvCfg where
  M : Mod
  acc : Nat
  base : Nat
  tbl : Nat
  B : Nat
  C : Nat
  Cn : Nat

namespace InvCfg

variable (P : InvCfg)

/-- Words of `f`, `g` (`n + 1`). -/
def L : Nat := P.M.n + 1

/-- The slots (byte offsets): `f`, `g`, `a`, `b`, the staging `f'`, `g'`, the
temporary `t` (`n + 2` words), the masked operands `U` (`n + 1`), and the
constant `C` (in `f'`'s place); a word past them is unused. -/
def sF : Nat := P.tbl
def sG : Nat := P.tbl + 8 * P.L
def sA : Nat := P.tbl + 16 * P.L
def sB : Nat := P.sA + 8 * P.M.n
def sNF : Nat := P.sB + 8 * P.M.n
def sNG : Nat := P.sNF + 8 * P.L
def sT : Nat := P.sNG + 8 * P.L
def sU : Nat := P.sT + 8 * (P.M.n + 2)
def sC : Nat := P.sNF

/-- `d = rbx = 1`, the count `r14 = B`; `f = p`, `g = x` (a zero word on top),
`a = 0`, `b = 1`. -/
def init : List Instr :=
  [.mov32 .rbx (.imm 1), .mov32 .r14 (.imm (BitVec.ofNat 32 P.B))] ++
  copy P.M.n P.sF P.M.mo ++ zeroTop P.sF P.M.n ++ copy P.M.n P.sG P.base ++ zeroTop P.sG P.M.n ++
  zeroWords P.M.n P.sA ++ zeroWords P.M.n P.sB ++ [.mov32 .r8 (.imm 1), .store (sc P.sB) .r8]

/-- A batch's start: the low words of `f`, `g` into `[sT]`, `[sT + 8]`, and `rbx = ~d`. -/
def batchStart : List Instr :=
  copy 1 P.sT P.sF ++ copy 1 (P.sT + 8) P.sG ++ [.alu .xor .rbx (.imm (-1))]

/-- `59` divsteps from `d` in `rbx` and the low words of `f`, `g`: `d` and
their matrix in `rbx`, `r9`–`r12`. -/
def words : List Instr :=
  P.batchStart ++ pchunk P.sT 15 true false ++ pchunk P.sT 15 false false ++ pchunk P.sT 15 false false ++
    pchunk P.sT 14 false true ++ [.alu .xor .rbx (.imm (-1))]

/-- `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
def fgUpdate : List Instr :=
  lin .r9 .r10 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNF P.sT P.L ++
  lin .r11 .r12 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNG P.sT P.L ++
  copy P.L P.sF P.sNF ++ copy P.L P.sG P.sNG

/-- `(a, b) := (u a + v b, q a + r b) / 2^64 mod p`; `a` staged in `f'`. -/
def abUpdate : List Instr :=
  lin .r9 .r10 P.sT P.sA P.sB P.sU P.M.n P.L ++ mredC P.M P.sNF P.sT P.sU ++
  lin .r11 .r12 P.sT P.sA P.sB P.sU P.M.n P.L ++ mredC P.M P.sB P.sT P.sU ++
  copy P.M.n P.sA P.sNF

/-- The count of batches less one, its zero flag for the loop. -/
def batchEnd : List Instr := [.alu .sub .r14 (.imm 1)]

/-- Whether the updates are in registers (`updX`): four words with BMI2 and ADX. -/
def regs : Bool := P.M.n == 4 && P.M.adx

/-- Both updates in registers: `d` kept at `[U]` meanwhile; `f'` and `a'`
staged in `[f']`, `g'` and `b'` written in place. -/
def updX : List Instr :=
  [.store (sc P.sU) .rbx] ++
  fHalfX .r9 .r10 P.sF P.sG P.sNF ++ fHalfX .r11 .r12 P.sF P.sG P.sG ++ copy P.L P.sF P.sNF ++
  abHalfX P.M .r9 .r10 P.sA P.sB P.sNF ++ abHalfX P.M .r11 .r12 P.sA P.sB P.sB ++
  copy P.M.n P.sA P.sNF ++ [.mov .rbx (.mem (sc P.sU))]

/-- A batch. -/
def batch : Prog isa :=
  .block (P.words ++ (if P.regs then P.updX else P.fgUpdate ++ P.abUpdate) ++ batchEnd)

/-- The end: `f = ±1`; `[C] = C` if `f > 0`, else `Cn = p - C`, and `acc = a [C] / R`. -/
def finish : List Instr :=
  [.mov .rdx (.mem (sc P.sF))] ++ maskOf .rcx .rdx ++
  ((List.range P.M.n).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
      .store (sc (P.sC + 8 * i)) .rax]) ++
  Mont.X86_64.mul P.M P.acc P.sA P.sC

/-- The inversion modulo `m` (`n ≤ 9` words): `10` batches for up to 256
bits, `15` for 384 and `23` for 576 (`590`, `885` and `1357` divsteps), and
`C = 2^(5 B) R³ mod m`. -/
def ofMod (M : Mod) (acc base tbl m : Nat) : InvCfg :=
  let B := if M.n ≤ 4 then 10 else if M.n ≤ 6 then 15 else 23
  let C := 2 ^ (5 * B) * (2 ^ (64 * M.n)) ^ 3 % m
  { M, acc, base, tbl, B, C, Cn := m - C }

/-- `[acc] = [base]^(p - 2)`. -/
def inv : Prog isa :=
  .seq (.block P.init) (.seq (.loop P.batch .ne) (.block P.finish))

end InvCfg

end VG.Impl.Weierstrass.X86_64
