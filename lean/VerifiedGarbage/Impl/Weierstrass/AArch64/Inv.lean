module

public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Short Weierstrass curves on AArch64: inversion by divsteps

`[acc] = [base]^(p - 2)` for a prime `p` (`InvCfg.inv`), as the inverse of
`[base]` (zero for zero) by Bernstein–Yang divsteps in batches of `N = 59`
(`Proof/Divstep/Alg.lean`'s `invRun`), then one Montgomery multiplication by
a constant. Nothing depends on the numbers but through masks.

* `f`, `g`: `n + 1` words each (two's complement), from `(p, x)`.
* `a`, `b`: `n` words each in `[0, p)`, from `(0, 1)`; `f ≡ x a K`,
  `g ≡ x b K` modulo `p`.
* a batch: `d` in `x1` and the low words of `f` and `g`, `N` word divsteps
  (`wstepCode`, `Proof/Divstep/Word.lean`'s `wstep`) give the matrix
  `(u, v, q, r)` (`x4`–`x7`); `(f, g) := (u f + v g, q f + r g) / 2^N`
  exactly, `(a, b) := (u a + v b, q a + r b) / 2^64 mod p`.
* the end: `f = ±1`, `res = ±a ≡ x⁻¹ 2^(-5 B)`, and `acc = res C / R` for
  `C = 2^(5 B) R³ mod p`.

The words of `f`, `g`, `a`, `b` and the temporaries are in the table area of
the powers' configuration (`tbl`, `9 n` words).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

/-! ## The word divstep

`d` in `x1`, the words of `f` and `g` in `x2`, `x3`, the matrix `u, v, q, r`
in `x4`–`x7`; `x11 = 1`, `x12 = 0`; through `x8`–`x10`. -/

/-- One divstep on words, branch-free by the flags: `x8`–`x10` are the
addends of `g`, `q`, `r` (`f`, `u`, `v`, negated if `d ≥ 0`, and zero if `g`
is even), `ge` after the `ccmp` says that the step swaps (`g` odd and
`d ≥ 0`), and then `f, u, v` take `g, q, r`'s. -/
def wstepCode : List Instr :=
  [.tst .x .x1 .x1, .csneg .x .x8 .x2 .x2 .lt, .csneg .x .x9 .x4 .x4 .lt, .csneg .x .x10 .x5 .x5 .lt,
    .tst .x .x3 .x11, .cselc .x .x8 .x8 .x12 .ne, .cselc .x .x9 .x9 .x12 .ne, .cselc .x .x10 .x10 .x12 .ne,
    .ccmp .x .x1 0 8 .ne, .cselc .x .x2 .x3 .x2 .ge, .cselc .x .x4 .x6 .x4 .ge, .cselc .x .x5 .x7 .x5 .ge,
    .csneg .x .x1 .x1 .x1 .lt, .add .x .x3 .x3 .x8, .add .x .x6 .x6 .x9, .add .x .x7 .x7 .x10,
    .addImm .x .x1 .x1 2, .lsr .x .x3 .x3 1, .lsl .x .x4 .x4 1, .lsl .x .x5 .x5 1]

/-- `N` word divsteps, counted down in `x13`. -/
def wsteps (N : Nat) : Prog isa :=
  .seq (.block [.movz .x .x13 (BitVec.ofNat 16 N) 0])
    (.loop (.block (.subImm .x .x13 .x13 1 :: wstepCode)) (.nonzero .x .x13))

/-! ## Numbers of several words in memory

At byte offsets of `x0`, little-endian; through `x2`, `x3`, `x8`–`x10`, with
`x12 = 0`. -/

/-- `[dst] = 0` (`k` words). -/
def zerosW (dst k : Nat) : List Instr := (List.range k).map fun i => st .x12 (dst + 8 * i)

/-- Word `i` of `w [src]`: `x10` the high word carried. -/
def mulwStep (w : Reg) (dst src i : Nat) : List Instr :=
  if i = 0 then [ld .x2 src, .mul .x .x8 w .x2, .umulh .x10 w .x2, st .x8 dst]
  else [ld .x2 (src + 8 * i), .mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10,
    .adc .x .x10 .x9 .x12, st .x8 (dst + 8 * i)]

/-- `[dst] = w [src] mod 2^(64 K)` (`[dst]` of `K` words, `[src]` of `1 ≤ k ≤ K`):
`x10` carries the high word. -/
def mulw (w : Reg) (dst src k K : Nat) : List Instr :=
  (List.range k).flatMap (mulwStep w dst src) ++
  (if k < K then st .x10 (dst + 8 * k) :: zerosW (dst + 8 * (k + 1)) (K - k - 1) else [])

/-- Word `i` of `[dst] += w [src]`: `x10` the high word carried. -/
def mulAddStep (w : Reg) (dst src i : Nat) : List Instr :=
  [ld .x2 (src + 8 * i), .mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10,
    .adc .x .x9 .x9 .x12, ld .x3 (dst + 8 * i), .adds .x .x3 .x3 .x8, .adc .x .x10 .x9 .x12,
    st .x3 (dst + 8 * i)]

/-- Word `k + 1 + i` of the carry's propagation. -/
def carryStep (dst k i : Nat) : List Instr :=
  [ld .x3 (dst + 8 * (k + 1 + i)), .adcs .x .x3 .x3 .x12, st .x3 (dst + 8 * (k + 1 + i))]

/-- `[dst] += w [src] mod 2^(64 K)` (`[dst]` of `K` words, `[src]` of `k ≤ K`):
`x10` carries the high word. -/
def mulAdd (w : Reg) (dst src k K : Nat) : List Instr :=
  [.movz .x .x10 0 0] ++ (List.range k).flatMap (mulAddStep w dst src) ++
  (if k < K then
    [ld .x3 (dst + 8 * k), .adds .x .x3 .x3 .x10, st .x3 (dst + 8 * k)] ++
    (List.range (K - k - 1)).flatMap (carryStep dst k)
  else [])

/-- Word `i + 1` of `[dst] -= 2^64 ([src] & m)`. -/
def subShStep (m : Reg) (dst src i : Nat) : List Instr :=
  [ld .x3 (dst + 8 * (i + 1)), ld .x2 (src + 8 * i), .logic .and .x .x2 .x2 m,
    if i = 0 then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2, st .x3 (dst + 8 * (i + 1))]

/-- `[dst] -= 2^64 ([src] & m) mod 2^(64 K)` (`[dst]` of `K ≥ 2` words, words
`0 … K - 2` of `[src]`; the mask `m` all ones or zero). -/
def subSh (m : Reg) (dst src K : Nat) : List Instr :=
  (List.range (K - 1)).flatMap (subShStep m dst src)

/-- `d = -(src >> 63)`, the mask of `src`'s sign (`x12 = 0`). -/
def maskOf (d src : Reg) : List Instr := [.lsr .x d src 63, .sub .x d .x12 d]

/-- `x9 = -(x3 >> 63)`, the mask of `x3`'s sign. -/
def sgnMask : List Instr := [.lsr .x .x9 .x3 63, .sub .x .x9 .x12 .x9]

/-- Word `i` of `[src] / 2^59`, from words `i` and `i + 1`. -/
def shrStep (dst src i : Nat) : List Instr :=
  [ld .x2 (src + 8 * i), ld .x3 (src + 8 * (i + 1)), .extr .x .x8 .x3 .x2 59, st .x8 (dst + 8 * i)]

/-- `[dst] = [src] / 2^59` (arithmetic, `L` words each). -/
def shr59 (dst src L : Nat) : List Instr :=
  (List.range (L - 1)).flatMap (shrStep dst src) ++
  [ld .x3 (src + 8 * (L - 1))] ++ sgnMask ++
  [.extr .x .x8 .x9 .x3 59, st .x8 (dst + 8 * (L - 1))]

/-- `[t] = w [x] + w' [y]`, signed, modulo `2^(64 K)`: unsigned products, less
`2^64 [x]` for a negative `w` (mask `mw`) and `2^64 [y]` for a negative `w'`. -/
def lin (w w' mw mw' : Reg) (t x y k K : Nat) : List Instr :=
  mulw w t x k K ++ mulAdd w' t y k K ++ subSh mw t x K ++ subSh mw' t y K

/-- Word `i` of a copy. -/
def copyStep (dst src i : Nat) : List Instr := [ld .x2 (src + 8 * i), st .x2 (dst + 8 * i)]

/-- `[dst] = [src]` (`k` words) through `x2`. -/
def copyW (dst src k : Nat) : List Instr := (List.range k).flatMap (copyStep dst src)

/-- Word `i` of `p & m` (`m` a mask, or none), `0` for `i = n`, into `x2`. -/
def opnd (m : Option Reg) (mo n i : Nat) : List Instr :=
  if i < n then ld .x2 (mo + 8 * i) :: (match m with | some r => [.logic .and .x .x2 .x2 r] | none => [])
  else [.add .x .x2 .x12 .x12]

/-- Word `i` of `[d] ± (p & m)`. -/
def chainStep (sub : Bool) (m : Option Reg) (d mo n i : Nat) : List Instr :=
  [ld .x3 (d + 8 * i)] ++ opnd m mo n i ++
  [if sub then (if i = 0 then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2)
    else (if i = 0 then .adds .x .x3 .x3 .x2 else .adcs .x .x3 .x3 .x2), st .x3 (d + 8 * i)]

/-- `[d] = [d] ± (p & m) mod 2^(64 (n + 1))` (`n + 1` words; `p` the `n` words at `mo`). -/
def chain (sub : Bool) (m : Option Reg) (d mo n : Nat) : List Instr :=
  (List.range (n + 1)).flatMap (chainStep sub m d mo n)

/-- `k = t₀ m mod 2^64` into `x16`, and `[t]` sign-extended to `n + 2` words. -/
def mredHead (M : Mod) (t : Nat) : List Instr :=
  [ld .x2 t] ++ const64 .x17 M.minv ++ [.mul .x .x16 .x2 .x17, ld .x3 (t + 8 * M.n)] ++ sgnMask ++
  [st .x9 (t + 8 * (M.n + 1))]

/-- `[dst] = mred [t]` (`n` words; `[t]` of `n + 1` words, signed, with room
for one more): `[t] += k p` for `k = t₀ m mod 2^64` (`[t]` sign-extended to
`n + 2` words), then `r =` words `1 … n + 1` brought into `[0, p)`: plus `p`
if negative, less `p`, and plus `p` if that is negative. -/
def mredC (M : Mod) (dst t : Nat) : List Instr :=
  mredHead M t ++ mulAdd .x16 t M.mo M.n (M.n + 2) ++
  ([ld .x3 (t + 8 * (M.n + 1))] ++ sgnMask) ++ chain false (some .x9) (t + 8) M.mo M.n ++
  chain true none (t + 8) M.mo M.n ++
  ([ld .x3 (t + 8 * (M.n + 1))] ++ sgnMask) ++ chain false (some .x9) (t + 8) M.mo M.n ++
  copyW dst (t + 8) M.n

/-! ## The configuration -/

/-- Inversion's configuration: the field, the result and input slots, the
table area of `9 n` words, the number of batches, and the final constant. -/
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
temporary `t` (`n + 2` words), and the constant `C`. -/
def sF : Nat := P.tbl
def sG : Nat := P.tbl + 8 * P.L
def sA : Nat := P.tbl + 16 * P.L
def sB : Nat := P.sA + 8 * P.M.n
def sNF : Nat := P.sB + 8 * P.M.n
def sNG : Nat := P.sNF + 8 * P.L
def sT : Nat := P.sNG + 8 * P.L
def sC : Nat := P.sNF

/-- `x11 = 1`, `x12 = 0`, `x1 = d = 1`, `x19 = B`; `f = p`, `g = x`, `a = 0`, `b = 1`. -/
def init : List Instr :=
  [.movz .x .x11 1 0, .movz .x .x12 0 0, .movz .x .x1 1 0,
    .movz .x .x19 (BitVec.ofNat 16 P.B) 0] ++
  copyW P.sF P.M.mo P.M.n ++ [st .x12 (P.sF + 8 * P.M.n)] ++
  copyW P.sG P.base P.M.n ++ [st .x12 (P.sG + 8 * P.M.n)] ++
  zerosW P.sA P.M.n ++ zerosW P.sB P.M.n ++ [st .x11 P.sB]

/-- A batch's start: the low words of `f`, `g` and the identity. -/
def batchStart : List Instr :=
  [decCounter, .movz .x .x11 1 0, .movz .x .x12 0 0, ld .x2 P.sF, ld .x3 P.sG,
    .movz .x .x4 1 0, .movz .x .x5 0 0, .movz .x .x6 0 0, .movz .x .x7 1 0]

/-- `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
def fgUpdate : List Instr :=
  maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sT P.sF P.sG P.L P.L ++
    shr59 P.sNF P.sT P.L ++
  maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sT P.sF P.sG P.L P.L ++
    shr59 P.sNG P.sT P.L ++
  copyW P.sF P.sNF P.L ++ copyW P.sG P.sNG P.L

/-- `(a, b) := (u a + v b, q a + r b) / 2^64 mod p`; `a` staged in `f'`. -/
def abUpdate : List Instr :=
  maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sT P.sA P.sB P.M.n P.L ++
    mredC P.M P.sNF P.sT ++
  maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sT P.sA P.sB P.M.n P.L ++
    mredC P.M P.sB P.sT ++
  copyW P.sA P.sNF P.M.n

/-- A batch. -/
def batch : Prog isa :=
  .seq (.block P.batchStart) (.seq (wsteps 59) (.block ((.movz .x .x12 0 0 :: P.fgUpdate) ++ P.abUpdate)))

/-- The end: `f = ±1`; `[C] = C` if `f > 0`, else `Cn = p - C`, and `acc = a [C] / R`. -/
def finish : List Instr :=
  [.movz .x .x12 0 0, ld .x3 P.sF] ++ sgnMask ++
  ((List.range P.M.n).flatMap fun i =>
    const64 .x2 (BitVec.ofNat 64 (P.C >>> (64 * i))) ++ const64 .x3 (BitVec.ofNat 64 (P.Cn >>> (64 * i))) ++
    [.logic .eor .x .x3 .x3 .x2, .logic .and .x .x3 .x3 .x9, .logic .eor .x .x2 .x2 .x3, st .x2 (P.sC + 8 * i)]) ++
  Mont.AArch64.mul P.M P.acc P.sA P.sC

/-- The inversion modulo `m` (`n ≤ 9` words): `10` batches for up to 256
bits, `15` for 384, `23` for 576 (`590`, `885` and `1328` divsteps), and
`C = 2^(5 B) R³ mod m`. -/
def ofMod (M : Mod) (acc base tbl m : Nat) : InvCfg :=
  let B := if M.n ≤ 4 then 10 else if M.n ≤ 6 then 15 else 23
  let C := 2 ^ (5 * B) * (2 ^ (64 * M.n)) ^ 3 % m
  { M, acc, base, tbl, B, C, Cn := m - C }

/-- `[acc] = [base]^(p - 2)`. -/
def inv : Prog isa :=
  .seq (.block P.init) (.seq (.loop P.batch (.nonzero .x .x19)) (.block P.finish))

end InvCfg

end VG.Impl.Weierstrass.AArch64
