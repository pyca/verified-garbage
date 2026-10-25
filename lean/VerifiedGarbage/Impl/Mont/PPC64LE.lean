module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Mont.Mod

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on PPC64LE

Arithmetic modulo an odd `m < 2^(64 n)`, on numbers below `m` held in the
working space, whose base is in `r3`, as `n` little-endian 64-bit words at
a constant offset, or at a register (`[a]` at `r5`, `[b]` at `r6`, `[o]` at
`r4`). The modulus `[M.mo]` is read through `r7 = r3 + M.mo` (`setMo`),
since `ld` takes only displacements that are multiples of 4.

The words are the digits of the arithmetic: `mulld` and `mulhdu` give the
low and high words of a product, and `addc`, `adde` and `addze` add with
XER's carry CA (`subfc` and `subfe` subtract with it, CA set when there is
no borrow). With `R = 2^(64 n)` and `m' = -m⁻¹ mod 2⁶⁴` (`M.minv`):

* `mul acc`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS) with the accumulator `T` in memory: `n + 1` words at
  `[acc]`, cleared, and `m'` stored above them. Each of the `n` iterations
  of the loop (counted down in `r8`; `r5` points to word `i` of `[a]`) does
  two rows: `T += u [b]` (`rowB`, `u = a_i` in `r9`), its top word, 0 or 1,
  in `r12`, then `T = (T + q m) / 2⁶⁴` (`rowM`) for `q = t₀ m' mod 2⁶⁴`,
  which clears `T`'s low word, each word stored one word down. A step of a
  row (`macStep`) adds the product `x y_j`, the carry word `r0` and the word
  `t_j`: the low word of the product with `addc` into the high word with
  `addze`, then `t_j` the same way; the sum is below `2¹²⁸`, and its high
  word is the next carry word. `T` is then below `2m` and reduced by
  `csub`.
* `add acc`: `[a] + [b]` at `[acc]` (`n` words, and the carry as a top
  word), then `csub`.
* `sub acc`: `[a] - [b]` at `[acc]`, its borrow as a mask (`subfe` of a
  register from itself), and `[a] - [b] + m` at `[M.tmp]`; the mask selects
  the second if `[a] - [b]` borrowed.
* `csub src`: the number below `2m` at `[src]` (`n` words and a top word,
  0 or 1) reduced modulo `m` into `[o]`: its difference with `m` is stored
  in `[M.tmp]`; the top word plus CA is 1 if it did not borrow, and its
  negation selects the difference or the number, a word at a time.

Every multiplication is `mulld` and `mulhdu`, every selection a mask, and
every address `r3`, `r4`, `r5`, `r6` or `r7` plus a constant (`r5` advanced
by 8 by the loop): nothing but the pointers may affect timing. The
operations use `r0`, `r5` and `r7`–`r12`, and write only `[o]`, `[acc]` and
`[M.tmp]`.
-/

@[expose] public section

namespace VG.Impl.Mont.PPC64LE

open VG.PPC64LE

/-- The working space's base. -/
abbrev wb : Reg := .r3

/-- `d = x`, a 32-bit constant, sign-extended (`lis`, `ori`): its low 32
bits are `x`. -/
def movImm (d : Reg) (x : BitVec 32) : List Instr :=
  [.lis d (x.extractLsb' 16 16), .ori d d (x.extractLsb' 0 16)]

/-- `r0 = 2³² - 1`. -/
def mask32 : List Instr := [.li .r0 0, .ori .r0 .r0 0xffff, .oris .r0 .r0 0xffff]

/-- `r7 = r3 + M.mo`: the modulus's pointer. -/
def setMo (M : Mod) : Instr := .addi .r7 wb M.mo

/-- `[r3 + dst + 8j] = r9 · [rs + src + 8j] + r0 + [r3 + rd + 8j]`, its low
word stored and its high word to `r0` (a multiply-accumulate step, which
never overflows), through `r10` and `r11` only. -/
def macStep (rs : Reg) (src rd dst j : Nat) : List Instr :=
  [.load .d .r11 rs (src + 8 * j), .mulhu .r10 .r9 .r11, .mul .r11 .r9 .r11, .addc .r11 .r11 .r0,
    .addze .r10 .r10, .load .d .r0 wb (rd + 8 * j), .addc .r11 .r11 .r0, .addze .r0 .r10,
    .store .d .r11 wb (dst + 8 * j)]

/-- `k` steps of a row. -/
def macs (rs : Reg) (src rd dst k : Nat) : List Instr := (List.range k).flatMap (macStep rs src rd dst)

/-- The row `T += u [b]`, for word `r5` of `[a]` (`[b]` at `r6`): `n` steps,
then the carry word added into word `n`, and the carry out, the top word, to
`r12`. -/
def rowB (n acc : Nat) : List Instr :=
  [.load .d .r9 .r5 0, .li .r0 0] ++ macs .r6 0 acc acc n ++
  ([.load .d .r10 wb (acc + 8 * n), .addc .r10 .r10 .r0, .store .d .r10 wb (acc + 8 * n), .li .r12 0,
    .addze .r12 .r12] : List Instr)

/-- The row `T = (T + q m) / 2⁶⁴` for `q = t₀ m' mod 2⁶⁴` (`m'` at
`[acc + 8 (n + 1)]`, the modulus at `r7`, the top word in `r12`): the low
word of `t₀ + q m₀`, zero, is dropped, and the other words are stored one
word down. -/
def rowM (M : Mod) (acc : Nat) : List Instr :=
  ([.load .d .r11 wb acc, .load .d .r10 wb (acc + 8 * (M.n + 1)), .mul .r9 .r11 .r10, .load .d .r10 .r7 0,
    .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 .r11, .addze .r0 .r0] : List Instr) ++
  macs .r7 8 (acc + 8) acc (M.n - 1) ++
  ([.load .d .r10 wb (acc + 8 * M.n), .addc .r10 .r10 .r0, .store .d .r10 wb (acc + 8 * (M.n - 1)),
    .addze .r12 .r12, .store .d .r12 wb (acc + 8 * M.n)] : List Instr)

/-- An iteration of `mul`: the two rows, then `r5` up a word, and the
count. -/
def row (M : Mod) (acc : Nat) : List Instr :=
  rowB M.n acc ++ rowM M acc ++ ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)

/-- `[r3 + acc]`, `k` words, cleared (through `r11`). -/
def zeros (acc k : Nat) : List Instr :=
  .li .r11 0 :: (List.range k).map fun j => .store .d .r11 wb (acc + 8 * j)

/-- The carrying operation of a step of a chain: `subfc`/`subfe` for a
difference, `addc`/`adde` for a sum, the first without a carry in. -/
def carryOp : Bool → Bool → Reg → Reg → Reg → Instr
  | false, true => .addc
  | false, false => .adde
  | true, true => .subc
  | true, false => .sube

/-- Word `j` of `[ra + da] ± [rb + db]`, with CA, to `[r3 + dd + 8j]`. -/
def chainStep (sub : Bool) (ra : Reg) (da : Nat) (rb : Reg) (db dd j : Nat) : List Instr :=
  [.load .d .r11 ra (da + 8 * j), .load .d .r12 rb (db + 8 * j), carryOp sub (j == 0) .r11 .r11 .r12,
    .store .d .r11 wb (dd + 8 * j)]

/-- The low `k` words of `[ra + da] ± [rb + db]` to `[r3 + dd]`, the carry
(or no borrow) in CA. -/
def chain (sub : Bool) (ra : Reg) (da : Nat) (rb : Reg) (db dd k : Nat) : List Instr :=
  (List.range k).flatMap (chainStep sub ra da rb db dd)

/-- Word `k` of the number at `[r3 + src]`, or of `[r3 + M.tmp]` where the
mask `r10` is all ones, to `[r4 + 8k]`. -/
def selWord (M : Mod) (src k : Nat) : List Instr :=
  [.load .d .r11 wb (src + 8 * k), .load .d .r12 wb (M.tmp + 8 * k), .logic .xor .r12 .r12 .r11,
    .logic .and .r12 .r12 .r10, .logic .xor .r11 .r11 .r12, .store .d .r11 .r4 (8 * k)]

/-- The selections of the `k` words. -/
def sels (M : Mod) (src k : Nat) : List Instr := (List.range k).flatMap (selWord M src)

/-- The number at `[r3 + src]` (`n` words, then a top word 0 or 1), below
`2m`, reduced modulo `m` (at `r7`) into `[r4]`: the difference with `m` to
`[M.tmp]`; `r10` is 1 if it did not borrow, and its negation selects it. -/
def csub (M : Mod) (src : Nat) : List Instr :=
  chain true wb src .r7 0 M.tmp M.n ++
  ([.load .d .r11 wb (src + 8 * M.n), .addze .r10 .r11, .li .r11 0, .sub .r10 .r11 .r10] : List Instr) ++
  sels M src M.n

/-- `[r3 + o] = x`, `n` 64-bit words, as `2n` 32-bit words through `r11`. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range (2 * n)).flatMap fun j =>
    movImm .r11 (BitVec.ofNat 32 (x >>> (32 * j))) ++ ([.store .w .r11 wb (o + 4 * j)] : List Instr)

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, through the accumulator at `[r3 + acc]`
(`[r4]` may be `[r5]` or `[r6]`). -/
def mul (M : Mod) (acc : Nat) : Prog isa :=
  .seq (.block (setConst 1 (acc + 8 * (M.n + 1)) M.minv.toNat ++ zeros acc (M.n + 1) ++ [setMo M, .li .r8 M.n])) <|
  .seq (.loop (.block (row M acc)) (.nonzero .d .r8)) <|
    .block (csub M acc)

/-- `[r4] = [r5] + [r6] mod m`. -/
def add (M : Mod) (acc : Nat) : List Instr :=
  setMo M :: chain false .r5 0 .r6 0 acc M.n ++
  ([.li .r10 0, .addze .r10 .r10, .store .d .r10 wb (acc + 8 * M.n)] : List Instr) ++ csub M acc

/-- `[r4] = [r5] - [r6] mod m`: `[r5] - [r6]`, and `m` added back where it
borrowed (the mask `r10`). -/
def sub (M : Mod) (acc : Nat) : List Instr :=
  setMo M :: chain true .r5 0 .r6 0 acc M.n ++ ([.sube .r10 .r10 .r10] : List Instr) ++
  chain false wb acc .r7 0 M.tmp M.n ++ sels M acc M.n

end VG.Impl.Mont.PPC64LE
