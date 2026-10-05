import VerifiedGarbage.Impl.Weierstrass.X86_64

/-!
# Short Weierstrass curves on x86-64: inversion by divsteps

`[acc] = [base]^(p - 2)` for a prime `p` (`InvCfg.inv`), as the inverse of
`[base]` (zero for zero) by Bernstein–Yang divsteps in batches of `N = 59`
(`Proof/Divstep/Alg.lean`'s `invRun`), then one Montgomery multiplication by
a constant: the algorithm of `Impl/Weierstrass/AArch64/Inv.lean`. Nothing
depends on the numbers but through masks.

* `f`, `g`: `n + 1` words each (two's complement), from `(p, x)`.
* `a`, `b`: `n` words each in `[0, p)`, from `(0, 1)`; `f ≡ x a K`,
  `g ≡ x b K` modulo `p`.
* a batch: `d` in `rbx` and the low words of `f` and `g` in `rcx` and `rbp`,
  `N` word divsteps (`wstepCode`, `Proof/Divstep/Word.lean`'s `wstep`) give
  the matrix `(u, v, q, r)` in `r9`–`r12`; `(f, g) := (u f + v g, q f + r g) / 2^N`
  exactly, `(a, b) := (u a + v b, q a + r b) / 2^64 mod p`.
* the end: `f = ±1`, `res = ±a ≡ x⁻¹ 2^(-5 B)`, and `acc = res C / R` for
  `C = 2^(5 B) R³ mod p`.

The model has no left shift and no arithmetic right shift: a word doubles
by adding it to itself (`x << 5` is five doublings), and the mask of a
word's sign is `0 - (x >> 63)`. The signed
products of the matrix and the numbers are unsigned products by `mul`, less
the number shifted by a word for a negative entry (`lin`), and since `and`
clears the carry flag, the masked operands of a carry chain are copied out
first (`maskCopy`). The multi-word sums are the wide Montgomery
multiplication's rows (`memRow`, `chainW`). The registers are those of
`pow` (`rbx` and the multiplication's for 4 words: `rax`, `rcx`, `rdx`,
`rbp`, `r8`–`r13`); the batches' count is a word of the working area.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-! ## The word divstep

`d` in `rbx`, the words of `f` and `g` in `rcx`, `rbp`, the matrix `u, v, q, r`
in `r9`–`r12`; the masks `B` and `S` in `r13` and `r8`, through `rax`. -/

/-- `rax = ((src ^ S) - S) & B`, then `dst += rax`. -/
def condAdd (dst src : Reg) : List Instr :=
  [.mov .rax (.reg src), .alu .xor .rax (.reg .r8), .alu .sub .rax (.reg .r8), .alu .and .rax (.reg .r13),
    .alu .add dst (.reg .rax)]

/-- `dst += src & S`. -/
def swapAdd (dst src : Reg) : List Instr :=
  [.mov .rax (.reg src), .alu .and .rax (.reg .r8), .alu .add dst (.reg .rax)]

/-- One divstep on words. -/
def wstepCode : List Instr :=
  [.mov .r13 (.reg .rbp), .alu .and .r13 (.imm 1), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r13),
    .mov .r13 (.reg .rax),
    .mov .r8 (.reg .rbx), .shift .shr .r8 63, .alu .sub .r8 (.imm 1), .alu .and .r8 (.reg .r13)] ++
  condAdd .rbp .rcx ++ condAdd .r11 .r9 ++ condAdd .r12 .r10 ++
  swapAdd .rcx .rbp ++ swapAdd .r9 .r11 ++ swapAdd .r10 .r12 ++
  ([.alu .xor .rbx (.reg .r8), .alu .sub .rbx (.reg .r8), .alu .add .rbx (.imm 2),
    .shift .shr .rbp 1, .alu .add .r9 (.reg .r9), .alu .add .r10 (.reg .r10)] : List Instr)

/-- `N ≥ 1` word divsteps, counted down in `rdx`. -/
def wsteps (N : Nat) : Prog isa :=
  .seq (.block [.mov32 .rdx (.imm (BitVec.ofNat 32 N))])
    (.loop (.block (wstepCode ++ [.alu .sub .rdx (.imm 1)])) .ne)

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

/-- `r8 *= 32`, by five doublings. -/
def shl5 : List Instr := List.replicate 5 (.alu .add .r8 (.reg .r8))

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
temporary `t` (`n + 2` words), the masked operands `U` (`n + 1`), the count
of batches, and the constant `C` (in `f'`'s place). -/
def sF : Nat := P.tbl
def sG : Nat := P.tbl + 8 * P.L
def sA : Nat := P.tbl + 16 * P.L
def sB : Nat := P.sA + 8 * P.M.n
def sNF : Nat := P.sB + 8 * P.M.n
def sNG : Nat := P.sNF + 8 * P.L
def sT : Nat := P.sNG + 8 * P.L
def sU : Nat := P.sT + 8 * (P.M.n + 2)
def sCnt : Nat := P.sU + 8 * P.L
def sC : Nat := P.sNF

/-- `d = rbx = 1`, the count `B`; `f = p`, `g = x` (a zero word on top),
`a = 0`, `b = 1`. -/
def init : List Instr :=
  [.mov32 .rbx (.imm 1), .mov32 .rax (.imm (BitVec.ofNat 32 P.B)), .store (sc P.sCnt) .rax] ++
  copy P.M.n P.sF P.M.mo ++ zeroTop P.sF P.M.n ++ copy P.M.n P.sG P.base ++ zeroTop P.sG P.M.n ++
  zeroWords P.M.n P.sA ++ zeroWords P.M.n P.sB ++ [.mov32 .r8 (.imm 1), .store (sc P.sB) .r8]

/-- A batch's start: the low words of `f`, `g` and the identity. -/
def batchStart : List Instr :=
  [.mov .rcx (.mem (sc P.sF)), .mov .rbp (.mem (sc P.sG)), .mov32 .r9 (.imm 1), .mov32 .r10 (.imm 0),
    .mov32 .r11 (.imm 0), .mov32 .r12 (.imm 1)]

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
def batchEnd : List Instr :=
  [.mov .rax (.mem (sc P.sCnt)), .alu .sub .rax (.imm 1), .store (sc P.sCnt) .rax]

/-- A batch. -/
def batch : Prog isa :=
  .seq (.block P.batchStart) (.seq (wsteps 59) (.block (P.fgUpdate ++ P.abUpdate ++ P.batchEnd)))

/-- The end: `f = ±1`; `[C] = C` if `f > 0`, else `Cn = p - C`, and `acc = a [C] / R`. -/
def finish : List Instr :=
  [.mov .rdx (.mem (sc P.sF))] ++ maskOf .rcx .rdx ++
  ((List.range P.M.n).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
      .store (sc (P.sC + 8 * i)) .rax]) ++
  Mont.X86_64.mul P.M P.acc P.sA P.sC

/-- The inversion modulo `m` (`n ≤ 6` words): `10` batches for up to 256
bits, `15` for 384 (`590` and `885` divsteps), and `C = 2^(5 B) R³ mod m`. -/
def ofMod (M : Mod) (acc base tbl m : Nat) : InvCfg :=
  let B := if M.n ≤ 4 then 10 else 15
  let C := 2 ^ (5 * B) * (2 ^ (64 * M.n)) ^ 3 % m
  { M, acc, base, tbl, B, C, Cn := m - C }

/-- `[acc] = [base]^(p - 2)`. -/
def inv : Prog isa :=
  .seq (.block P.init) (.seq (.loop P.batch .ne) (.block P.finish))

end InvCfg

end VG.Impl.Weierstrass.X86_64
