module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch

/-!
# Products for the RSA key checks on PPC64LE

Two operations on the arrays of the key working space (`KeyWs.lean`), by
digits of 32 bits with 64-bit products (`InvBatch.macBody`), in place of a
bit-serial division or product:

* `mulLo o x y len`: `[o] := [x] [y] mod 2^(32 w)`, the schoolbook product
  truncated to `w` digits, over the `⌈len / 4⌉` low digits of `[x]` (`len`,
  a register, holds `x`'s length in bytes, at most `4 w`): digit `i` of `[x]`
  times the `w - i` low digits of `[y]`, added at digit `i` of `[o]`, the
  carry out of digit `w - 1` dropped.
* `montMul a x y m t len cnt`: `[a] := [x] [y] 2^(-32 c) mod [m]` for an odd
  `[m] < 2^(32 wd)`, `wd = ⌈len / 4⌉` (`len` holding `m`'s length in bytes,
  `wd ≤ w`), `[y] < [m]` and `[x] < 2^(32 c)`, `c ≥ 1` set into `r4` by
  `cnt`: Montgomery's multiplication by operands (CIOS), each of the `c`
  steps adding `x_i [y]` and `k [m]`, `k = a₀ (-m⁻¹) mod 2^32`, over
  `K = wd + 1` digits and the top digit `K`, then shifting `[a]` down by a
  digit; `[a] < 2 [m]` after each, and one subtraction where it does not
  borrow ends it below `[m]`. `-m⁻¹ mod 2^32` (`PublicChecked.minv`) is kept
  in digit 0 of the temporary `[t]`, which then holds the subtraction.

The pointers and counts depend only on `w`, the lengths and the base: the
addresses and branches are public. `r4`, `r10` and `r12` hold the count,
`x`'s pointer and `K` (or `mulLo`'s inner count).
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.MontKey

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.InvBatch

/-! ## `mulLo` -/

/-- The product's start: `[o]` zeroed (`w` digits), `x`'s pointer into
`r10`, its digits `⌈len / 4⌉` into `r4` and the inner count `w` into `r12`. -/
def mulLoInit (o : Nat) : List Instr :=
  ptr .r5 o ++ [.addi .r8 .r29 0, .li .r0 0]

/-- The counts and `x`'s pointer. -/
def mulLoSet (x : Nat) (len : Reg) : List Instr :=
  ptr .r10 x ++ [.addi .r4 len 3, .lsr .d .r4 .r4 2, .addi .r12 .r29 0]

/-- One row: digit `i` of `[x]` (at `r10`) times `[y]`'s `r12 = w - i` low
digits added at digit `i` of `[o]`, the carry dropped. -/
def mulLoRow (o x y : Nat) : Prog isa :=
  .seq (.block ([.load .w .r11 .r10 0] ++ ptr .r5 o ++ ptr .r6 x ++ [.sub .r6 .r10 .r6, .add .r5 .r5 .r6,
      .addi .r6 .r5 0] ++ ptr .r7 y ++ [.addi .r8 .r12 0, .li .r9 0]))
    (.seq (countLoop .r8 macBody) (.block [.addi .r10 .r10 4, .subi .r12 .r12 1, .subi .r4 .r4 1]))

/-- `[o] := [x] [y] mod 2^(32 w)`, over the `⌈len / 4⌉` digits of `[x]`. -/
def mulLo (o x y : Nat) (len : Reg) : Prog isa := seqs [
  .block (mulLoInit o), countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4],
  .block (mulLoSet x len), .loop (mulLoRow o x y) (.nonzero .d .r4)]

/-! ## `montMul` -/

/-- `-m⁻¹ mod 2^32` into digit 0 of `[t]`, `K = ⌈len / 4⌉ + 1` into `r12`,
`[a]` zeroed (`w + 2` digits) and `x`'s pointer into `r10`. -/
def montInit (a x m t : Nat) (len : Reg) : List Instr :=
  ptr .r10 m ++ VG.Impl.Bignum.PPC64LE.PublicChecked.minv ++ ptr .r5 t ++ [.store .w .r12 .r5 0,
    .addi .r12 len 3, .lsr .d .r12 .r12 2, .addi .r12 .r12 1] ++
  ptr .r10 x ++ ptr .r5 a ++ [.addi .r8 .r29 2, .li .r0 0]

/-- `[a] += x_i [y]` over `K` digits, the carry to digit `K` (which is zero). -/
def montAddX (a y : Nat) : Prog isa :=
  .seq (.block ([.load .w .r11 .r10 0] ++ ptr .r5 a ++ ptr .r6 a ++ ptr .r7 y ++ [.addi .r8 .r12 0, .li .r9 0]))
    (.seq (countLoop .r8 macBody) (.block [.store .w .r9 .r5 0]))

/-- `k = a₀ (-m⁻¹) mod 2^32`, and `[a] += k [m]` over `K` digits, the carry
added to digit `K`. -/
def montAddM (a m t : Nat) : Prog isa :=
  .seq (.block (ptr .r5 t ++ [.load .w .r3 .r5 0] ++ ptr .r5 a ++ [.load .w .r0 .r5 0, .mul .r11 .r0 .r3,
      .lsr .w .r11 .r11 0] ++ (ptr .r5 a ++ ptr .r6 a ++ ptr .r7 m ++ [.addi .r8 .r12 0, .li .r9 0])))
    (.seq (countLoop .r8 macBody) (.block [.load .w .r0 .r5 0, .add .r0 .r0 .r9, .store .w .r0 .r5 0]))

/-- `[a] := [a] / 2^32`: its digits `1 … K` moved down, digit `K` zeroed;
then `x`'s next digit and one step less. -/
def montShift (a : Nat) : Prog isa :=
  .seq (.block (ptr .r5 a ++ [.addi .r6 .r5 4, .addi .r8 .r12 0]))
    (.seq (countLoop .r8 copyBody) (.block (ptr .r5 a ++ [.lsl .r0 .r12 2, .add .r5 .r5 .r0, .li .r0 0,
      .store .w .r0 .r5 0, .addi .r10 .r10 4, .subi .r4 .r4 1])))

/-- One step of the multiplication. -/
def montStep (a y m t : Nat) : Prog isa := seqs [montAddX a y, montAddM a m t, montShift a]

/-- `[a] := [a] - [m]` where that does not borrow, over `K` digits, through
`[t]`. -/
def montFinal (a m t : Nat) : Prog isa := seqs [
  .block (ptr .r5 t ++ ptr .r6 a ++ ptr .r7 m ++ [.addi .r8 .r12 0, .li .r9 0]), countLoop .r8 subBody,
  .block (ptr .r5 a ++ ptr .r6 t ++ ptr .r7 a ++ [.addi .r8 .r12 0, .li .r0 0, .sub .r9 .r0 .r9]),
  countLoop .r8 selBody]

/-- Digit `w` of `[m]` and of `[y]` zeroed (their `w` digits unchanged), so
that their `K ≤ w + 1` digits are their values. -/
def montTops (m y : Nat) : List Instr :=
  ptr .r5 m ++ [.lsl .r0 .r29 2, .add .r5 .r5 .r0, .li .r3 0, .store .w .r3 .r5 0] ++
  ptr .r5 y ++ [.add .r5 .r5 .r0, .store .w .r3 .r5 0]

/-- `[a] := [x] [y] 2^(-32 c) mod [m]`, `c` steps set into `r4` by `cnt`, from
`[m]` and `[y]` with digit `w` zero. -/
def montCore (a x y m t : Nat) (len : Reg) (cnt : List Instr) : Prog isa := seqs [
  .block (montInit a x m t len), countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4],
  .block cnt, .loop (montStep a y m t) (.nonzero .d .r4), montFinal a m t]

/-- `[a] := [x] [y] 2^(-32 c) mod [m]`, `c` steps set into `r4` by `cnt`. -/
def montMul (a x y m t : Nat) (len : Reg) (cnt : List Instr) : Prog isa :=
  .seq (.block (montTops m y)) (montCore a x y m t len cnt)

/-- `w` steps, for `[x] < 2^(32 w)`. -/
def cntW : List Instr := [.addi .r4 .r29 0]

/-- `⌈len / 4⌉` steps, for `[x]` of `len` bytes. -/
def cntLen (len : Reg) : List Instr := [.addi .r4 len 3, .lsr .d .r4 .r4 2]

end VG.Impl.Rsa.PPC64LE.MontKey
