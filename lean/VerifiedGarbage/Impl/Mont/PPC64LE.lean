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

* `rmul acc`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS) with the accumulator `T` (`n + 1` words) in the registers
  `treg 0`, …, `treg n` (`r15` up), which it saves at `[acc]` first,
  clears, and restores last, and `m'` stored above them. Each of the `n`
  iterations of the loop (counted down in `r8`; `r5` points to word `i` of
  `[a]`) does two rows: `T += u [b]` (`rrowB`, `u = a_i` in `r9`), its top
  word, 0 or 1, in `r12`, then `T = (T + q m) / 2⁶⁴` (`rrowM`) for
  `q = t₀ m' mod 2⁶⁴`, which clears `T`'s low word, each word moved one
  register down. A step of a row (`rmac`) adds the product `x y_j`, the
  carry word `r0` and `t_j`: the low word of the product with `addc` into
  the high word with `addze`, then `t_j` the same way; the sum is below
  `2¹²⁸`, and its high word is the next carry word. `T` is then below `2m`
  and reduced as `csub` does (`rcsub`).
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
operations use `r0`, `r5` and `r7`–`r12` (and `rmul` the registers it
restores), and write only `[o]`, `[acc]` and `[M.tmp]`.
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

/-- `[r4] = [r5] + [r6] mod m`. -/
def add (M : Mod) (acc : Nat) : List Instr :=
  setMo M :: chain false .r5 0 .r6 0 acc M.n ++
  ([.li .r10 0, .addze .r10 .r10, .store .d .r10 wb (acc + 8 * M.n)] : List Instr) ++ csub M acc

/-- `[r4] = [r5] - [r6] mod m`: `[r5] - [r6]`, and `m` added back where it
borrowed (the mask `r10`). -/
def sub (M : Mod) (acc : Nat) : List Instr :=
  setMo M :: chain true .r5 0 .r6 0 acc M.n ++ ([.sube .r10 .r10 .r10] : List Instr) ++
  chain false wb acc .r7 0 M.tmp M.n ++ sels M acc M.n

/-! ## The multiplication -/

/-- The register of the accumulator's word `j`, for `j ≤ 9` (`r15`–`r24`).
They are callee-saved, so `rmul` restores them; but a restored register is
a loaded value, which the constant-time analysis takes as secret, so they
leave out `r14` and `r25`–`r31`, which callers keep public values in. -/
def treg (j : Nat) : Reg := [Reg.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24].getD j .r25

/-- `treg (dst + j) = r9 · [rs + src + 8j] + r0 + treg (rd + j)`, its high
word to `r0`, through `r10` and `r11`. -/
def rmac (rs : Reg) (src rd dst j : Nat) : List Instr :=
  [.load .d .r11 rs (src + 8 * j), .mulhu .r10 .r9 .r11, .mul .r11 .r9 .r11, .addc .r11 .r11 .r0,
    .addze .r10 .r10, .addc (treg (dst + j)) .r11 (treg (rd + j)), .addze .r0 .r10]

/-- `k` steps of a row. -/
def rmacs (rs : Reg) (src rd dst k : Nat) : List Instr := (List.range k).flatMap (rmac rs src rd dst)

/-- The row `T += u [b]`, for word `r5` of `[a]` (`[b]` at `r6`): `n` steps,
then the carry word added into `treg n`, and the carry out, the top word,
to `r12`. -/
def rrowB (n : Nat) : List Instr :=
  [.load .d .r9 .r5 0, .li .r0 0] ++ rmacs .r6 0 0 0 n ++
  ([.addc (treg n) (treg n) .r0, .li .r12 0, .addze .r12 .r12] : List Instr)

/-- The row `T = (T + q m) / 2⁶⁴` for `q = t₀ m' mod 2⁶⁴` (`m'` at
`[acc + 8 (n + 1)]`, the modulus at `r7`, the top word in `r12`): the low
word of `t₀ + q m₀`, zero, is dropped, and the other words are moved one
register down. -/
def rrowM (M : Mod) (acc : Nat) : List Instr :=
  ([.load .d .r10 wb (acc + 8 * (M.n + 1)), .mul .r9 (treg 0) .r10, .load .d .r10 .r7 0,
    .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 (treg 0), .addze .r0 .r0] : List Instr) ++
  rmacs .r7 8 1 0 (M.n - 1) ++
  ([.addc (treg (M.n - 1)) (treg M.n) .r0, .addze (treg M.n) .r12] : List Instr)

/-- An iteration of `rmul`. -/
def rrow (M : Mod) (acc : Nat) : List Instr :=
  rrowB M.n ++ rrowM M acc ++ ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)

/-- Word `j` of `T - m` (`T` in registers, `m` at `r7`), with CA, to
`[M.tmp + 8j]`. -/
def rsubStep (M : Mod) (j : Nat) : List Instr :=
  [.load .d .r12 .r7 (8 * j), carryOp true (j == 0) .r11 (treg j) .r12, .store .d .r11 wb (M.tmp + 8 * j)]

/-- Word `k` of `T`, or of `[M.tmp]` where the mask `r10` is all ones, to
`[r4 + 8k]`. -/
def rselWord (M : Mod) (k : Nat) : List Instr :=
  [.load .d .r12 wb (M.tmp + 8 * k), .logic .xor .r12 .r12 (treg k), .logic .and .r12 .r12 .r10,
    .logic .xor .r11 (treg k) .r12, .store .d .r11 .r4 (8 * k)]

/-- `T` (`n` words in registers, and the top word `treg n`, 0 or 1), below
`2m`, reduced modulo `m` (at `r7`) into `[r4]`, as `csub` does. -/
def rcsub (M : Mod) : List Instr :=
  (List.range M.n).flatMap (rsubStep M) ++
  ([.addze .r10 (treg M.n), .li .r11 0, .sub .r10 .r11 .r10] : List Instr) ++
  (List.range M.n).flatMap (rselWord M)

/-- The registers `treg 0`, …, `treg n` saved at `[acc]`. -/
def rsave (n acc : Nat) : List Instr := (List.range (n + 1)).map fun j => .store .d (treg j) wb (acc + 8 * j)

/-- … cleared. -/
def rzero (n : Nat) : List Instr := (List.range (n + 1)).map fun j => .li (treg j) 0

/-- … restored. -/
def rrestore (n acc : Nat) : List Instr := (List.range (n + 1)).map fun j => .load .d (treg j) wb (acc + 8 * j)

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, the accumulator in registers (`[r4]` may
be `[r5]` or `[r6]`). -/
def rmul (M : Mod) (acc : Nat) : Prog isa :=
  .seq (.block (setConst 1 (acc + 8 * (M.n + 1)) M.minv.toNat ++ rsave M.n acc ++ rzero M.n ++ [setMo M, .li .r8 M.n])) <|
  .seq (.loop (.block (rrow M acc)) (.nonzero .d .r8)) <|
    .block (rcsub M ++ rrestore M.n acc)

/-! ## Constants of 64 bits in registers -/

/-- `d = w` for `w < 2⁶⁴`: `li` for a small `w`, `lis`/`ori` for all ones,
else the high half (`lis`, `ori`), shifted up 32, then the low half's
halves (`oris`, `ori`). -/
def movImm64 (d : Reg) (w : Nat) : List Instr :=
  if w < 2 ^ 15 then [.li d w]
  else if w = 2 ^ 64 - 1 then [.lis d 0xffff, .ori d d 0xffff]
  else movImm d (BitVec.ofNat 32 (w >>> 32)) ++
    [.lsl d d 32, .oris d d (BitVec.ofNat 16 (w >>> 16)), .ori d d (BitVec.ofNat 16 w)]

/-- Word `j` of `m`. -/
def mword (m j : Nat) : Nat := (m >>> (64 * j)) % 2 ^ 64

/-! ## The multiplication of numbers of at most four words

`rmul4` is `rmul` with `[b]` in `bReg 0`, …, `bReg (n - 1)` (the registers
after the accumulator's) and the modulus in `mReg 0`, …, `mReg (n - 1)`
(`r6`, `r7`, `r10`, `r0`, once `[b]` and `m` are loaded), and each row as
two carry chains (`pass`): the low words of the products `x y_j` added in
one, then their high words one word up in another. A product's words then
need no carry of their own: a step is a multiplication and an `adde`. The
second row's high chain also moves the accumulator one register down. `m'`
is at `[M.tmp]` until the reduction. -/

/-- The registers of `[b]`, after the accumulator's. -/
def bReg (n j : Nat) : Reg := treg (n + 1 + j)

/-- The registers of the modulus. -/
def mReg (j : Nat) : Reg := [Reg.r6, .r7, .r10, .r0].getD j .r0

/-- The low (or high) word of `r9 · y j` through `r11`, added with CA into
`treg (ds + j)`, to `treg (dd + j)`. -/
def passStep (hi : Bool) (y : Nat → Reg) (dd ds j : Nat) : List Instr :=
  [if hi then .mulhu .r11 .r9 (y j) else .mul .r11 .r9 (y j), carryOp false (j == 0) (treg (dd + j)) (treg (ds + j)) .r11]

/-- `k` steps of a chain. -/
def pass (hi : Bool) (y : Nat → Reg) (dd ds k : Nat) : List Instr := (List.range k).flatMap (passStep hi y dd ds)

/-- The row `T += u [b]`, for word `r5` of `[a]`: the low words into
`treg 0`, …, the carry into `treg n` and from it to `r12`, then the high
words into `treg 1`, …, the carry into `r12`. -/
def qrowB (n : Nat) : List Instr :=
  [.load .d .r9 .r5 0] ++ pass false (bReg n) 0 0 n ++
  ([.addze (treg n) (treg n), .li .r12 0, .addze .r12 .r12] : List Instr) ++
  pass true (bReg n) 1 1 n ++ ([.addze .r12 .r12] : List Instr)

/-- `r9 = q = t₀ m' mod 2⁶⁴`: `t₀` itself for `m' = 1` (P-256's `p`), else
`t₀` times `m'` from `[M.tmp]`. -/
def qhead (M : Mod) : List Instr :=
  if M.minv.toNat = 1 then [.ori .r9 (treg 0) 0] else [.load .d .r11 wb M.tmp, .mul .r9 (treg 0) .r11]

/-- The row `T = (T + q m) / 2⁶⁴` for `q = t₀ m' mod 2⁶⁴` (`m'` at
`[M.tmp]`): the low words into `treg 0`, …, the carry into `treg n` and
`r12`, then the high words with the accumulator moved one register down,
`r12` into `treg n`. -/
def qrowM (M : Mod) : List Instr :=
  qhead M ++ pass false mReg 0 0 M.n ++
  ([.addze (treg M.n) (treg M.n), .addze .r12 .r12] : List Instr) ++
  pass true mReg 0 1 M.n ++ ([.addze (treg M.n) .r12] : List Instr)

/-- An iteration of `rmul4`. -/
def qrow (M : Mod) : List Instr := qrowB M.n ++ qrowM M ++ ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)

/-- Word `j` of `T - m` (`m` in registers), with CA, to `[M.tmp + 8j]`. -/
def qsubStep (M : Mod) (j : Nat) : List Instr :=
  [carryOp true (j == 0) .r11 (treg j) (mReg j), .store .d .r11 wb (M.tmp + 8 * j)]

/-- `T` (`n` words and the top word `treg n`, 0 or 1), below `2m`, reduced
modulo `m` (in registers) into `[r4]`. -/
def qcsub (M : Mod) : List Instr :=
  (List.range M.n).flatMap (qsubStep M) ++
  ([.addze .r10 (treg M.n), .li .r11 0, .sub .r10 .r11 .r10] : List Instr) ++
  (List.range M.n).flatMap (rselWord M)

/-- `[b]` to its registers, then the modulus `m` to its, as immediates. -/
def qload (M : Mod) (m : Nat) : List Instr :=
  (List.range M.n).map (fun j => .load .d (bReg M.n j) .r6 (8 * j)) ++
  (List.range M.n).flatMap (fun j => movImm64 (mReg j) (mword m j))

/-- `[r4] = [r5] [r6] R⁻¹ mod m` for `n ≤ 4`, the accumulator, `[b]` and
the modulus in registers (`[r4]` may be `[r5]` or `[r6]`). -/
def rmul4 (M : Mod) (m acc : Nat) : Prog isa :=
  .seq (.block (setConst 1 M.tmp M.minv.toNat ++ rsave (2 * M.n) acc ++ rzero M.n ++ qload M m ++ [.li .r8 M.n])) <|
  .seq (.loop (.block (qrow M)) (.nonzero .d .r8)) <|
    .block (qcsub M ++ rrestore (2 * M.n) acc)

/-- `rmul4` for at most four words, `rmul` for more: the two have the same
shape, so the choice is inside the blocks (and the code's shape, its frames
in particular, does not depend on it). -/
def rmulSel (M : Mod) (m acc : Nat) : Prog isa :=
  .seq (.block (if M.n ≤ 4 then
      setConst 1 M.tmp M.minv.toNat ++ rsave (2 * M.n) acc ++ rzero M.n ++ qload M m ++ [.li .r8 M.n]
    else setConst 1 (acc + 8 * (M.n + 1)) M.minv.toNat ++ rsave M.n acc ++ rzero M.n ++ [setMo M, .li .r8 M.n])) <|
  .seq (.loop (.block (if M.n ≤ 4 then qrow M else rrow M acc)) (.nonzero .d .r8)) <|
    .block (if M.n ≤ 4 then qcsub M ++ rrestore (2 * M.n) acc else rcsub M ++ rrestore M.n acc)

theorem rmulSel_eq (M : Mod) (m acc : Nat) : rmulSel M m acc = if M.n ≤ 4 then rmul4 M m acc else rmul M acc := by
  unfold rmulSel rmul4 rmul; split <;> rfl

/-! ## Sums and differences of at most four words, in registers

`add4` and `sub4` keep the words in `vReg 0`, …, `vReg (n - 1)` (`r7`–`r10`),
and the modulus is in no memory: each word of `m` is an immediate
(`movImm64`) where it is needed, so the function's entry stores none.

* `add4`: `[a] + [b]` (`ldStep`), the carry in `r0`, then `- m` in place
  (`subMStep`): it borrowed exactly when the carry plus CA is 0, so the mask
  `r11 = (r0 + CA) - 1` is all ones exactly when the sum was below `m`;
  then `m` under the mask added back, each word stored (`backStep`).
* `sub4`: `[a] - [b]`, the borrow's mask in `r11` (`subfe` of a register from
  itself), and `m` under it added back. -/

/-- The registers of a sum or difference. -/
def vReg (j : Nat) : Reg := [Reg.r7, .r8, .r9, .r10].getD j .r10

/-- Word `j` of `[r5] ± [r6]`, with CA, to `vReg j`. -/
def ldStep (sub : Bool) (j : Nat) : List Instr :=
  [.load .d .r11 .r5 (8 * j), .load .d .r12 .r6 (8 * j), carryOp sub (j == 0) (vReg j) .r11 .r12]

/-- Word `j` of `m` subtracted, with CA, from `vReg j`. -/
def subMStep (m j : Nat) : List Instr :=
  movImm64 .r12 (mword m j) ++ ([carryOp true (j == 0) (vReg j) (vReg j) .r12] : List Instr)

/-- Word `j` of `m` under the mask `r11` added, with CA, to `vReg j`, and
stored at `[r4 + 8j]`. -/
def backStep (m j : Nat) : List Instr :=
  movImm64 .r12 (mword m j) ++
    ([.logic .and .r12 .r12 .r11, carryOp false (j == 0) (vReg j) (vReg j) .r12, .store .d (vReg j) .r4 (8 * j)] :
      List Instr)

/-- `[r4] = [r5] + [r6] mod m`, for `n ≤ 4`. -/
def add4 (n m : Nat) : List Instr :=
  (List.range n).flatMap (ldStep false) ++ ([.li .r0 0, .addze .r0 .r0] : List Instr) ++
  (List.range n).flatMap (subMStep m) ++ ([.addze .r11 .r0, .subi .r11 .r11 1] : List Instr) ++
  (List.range n).flatMap (backStep m)

/-- `[r4] = [r5] - [r6] mod m`, for `n ≤ 4`. -/
def sub4 (n m : Nat) : List Instr :=
  (List.range n).flatMap (ldStep true) ++ ([.sube .r11 .r11 .r11] : List Instr) ++
  (List.range n).flatMap (backStep m)

end VG.Impl.Mont.PPC64LE
