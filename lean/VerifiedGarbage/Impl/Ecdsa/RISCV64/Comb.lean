module

public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.P256.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-!
# `[k]G` by the signed seven-bit comb on RISC-V

`vg_<curve>_mul_g(ws)`: `R = [k]G` for the scalar `k` at `K`'s slot, on the
layout of `Impl/Ecdsa/RISCV64.lean`, by the comb that the other targets
share (`Impl/Weierstrass/TCombWords.lean`, `Proof/Weierstrass/CombW.lean`):
with `k`'s windows `k_j` of seven bits (`j < 37`) and digits `k_j - 64`,
`[k]G = S + Σ_j [(k_j - 64) 2^(7j)]G` for the start `S = [64 Σ_j 2^(7j)]G`.
Table `j` of the static `VG_<CURVE>_COMB` holds `[m 2^(7j)]G` for
`m = 1 … 64` (entry `m - 1`: `x` then `y`, `n` words each, in Montgomery's
form, `16 n` bytes), the tables one after the other (`4096` bytes each for
`n = 4`).

From `R = S`, for `j` from 36 down to 0 (the counter `s1 = j + 1`, then `j`):

1. the window `k_j`: the bits `7j … 7j + 6` of the copy of `k` at `KC`
   followed by a zero word, by a funnel shift of the two words holding them
   (`w >>> r` or'ed with `(w' <<< 1) <<< (63 - r)`, for `r = 7j mod 64`,
   `63 - r` as `r XOR 63` in the low six bits that `sll` reads), and seven
   bits of it;
2. the digit `d = k_j - 64`, its sign's mask `σ` (`d` shifted right
   arithmetically by 63) and magnitude `m = (d XOR σ) - σ` (`0 … 64`), the
   entry's number `t = m - 1` and the mask of `m = 0` (`t` shifted right
   arithmetically by 63); the two masks are kept in `PT`'s slot, across the
   calls;
3. the masks of the six bits of `t` (`a1`–`a6`, each bit shifted to the top
   and arithmetically down), the table's address (in `s4`), plus `4096 j`,
   in `a0` and that plus 2048 in `a7`;
4. each of the entry's `2 n` quadwords selected from the 64 entries of the
   table (`scanWord`) without a secret address: a tree of selections
   `a XOR ((a XOR b) AND m)` (`pick`) over the 32 entries at `a0` and over
   the 32 at `a7`, each by the masks of bits 0 to 4 (`tree`), then between
   the two by the mask of bit 5; every load is an aligned `ld` (the table's
   address is a multiple of 64, `Abi.withConsts`) at an offset below 2048;
   the entry to `D` (`x`, then `y`), with `Z = 1`;
5. for `m = 0`, `D = (0 : 1 : 0)` instead, by the mask of `m = 0`
   (`sel`, from zero and one);
6. `-y` (the field's subtraction from zero) into `ACC`, and `y = -y` by the
   sign's mask;
7. `T = R + D` by the complete addition for `a = -3` (`rcb3`, with `b` at
   slot 40), copied to `R`.

The only branch is on the counter, and every address is `s0` plus a constant
(plus `8 (7j >>> 6)` for the window's words) or the table's address plus a
constant (plus `4096 j`): only the pointer may affect timing. The function
takes the table's address first (`lla`), and keeps it in `s4`, which its
callers do not use (the taint analysis takes a register restored from memory
for a secret); it keeps `s0`, `s1`, `s4` and `ra` past the numbered slots
(`mulSave`, slot 45, as `vg_<curve>_mul` does), and the copy of `k` in slot
46.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Comb

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- The slot of the copy of `k`, which a zero word follows. -/
def KC := 46

/-- The width of a window. -/
def w : Nat := 7

/-- The number of windows. -/
def J : Nat := 37

/-- The entries of a table: `2^(w-1)`. -/
def H : Nat := 64

/-- The register of the mask of bit `c` of the entry's number (`c < 6`). -/
def maskReg : Nat → Reg
  | 0 => .a1 | 1 => .a2 | 2 => .a3 | 3 => .a4 | 4 => .a5 | _ => .a6

/-- The registers of the selections. -/
def treeRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- `a := a XOR ((a XOR b) AND m)`: `b` where `m` is all ones, `a` where it
is zero. Clobbers `b`. -/
def pick (a b m : Reg) : List Instr := [.logic .xor b b a, .logic .and b b m, .logic .xor a a b]

/-- The selection among the `2 ^ L` quadwords at `base + o + stride e`
(`e < 2 ^ L`) by the masks of bits `0 … L - 1`, into the first of the
registers `rs` (`L + 1` of them, all clobbered): the two halves'
selections, then the second where bit `L - 1`'s mask is set. -/
def tree (base : Reg) (stride : Nat) : Nat → Nat → List Reg → List Instr
  | 0, o, a :: _ => [.load .d a base o]
  | L + 1, o, a :: b :: rs =>
    tree base stride L o (a :: b :: rs) ++ tree base stride L (o + stride * 2 ^ L) (b :: rs) ++
      pick a b (maskReg L)
  | _, _, _ => []

namespace Cfg

variable (c : Cfg)

/-- The bytes of an entry. -/
def eb : Nat := 16 * c.n

/-- Quadword `q` of the entry selected, into `t0`, then to `D` at `8 q`: the
32 entries at `a0` and the 32 at `a7`, then by the mask of bit 5. -/
def scanWord (q : Nat) : List Instr :=
  tree .a0 (eb c) 5 (8 * q) treeRegs ++ tree .a7 (eb c) 5 (8 * q) treeRegs.tail ++ pick .t0 .t1 (maskReg 5) ++
    [.store .d .t0 wb (c.sl DX + 8 * q)]

/-- The window `k_j` into `t2`, for `j` in `s1`: the funnel shift of the
words `7j >>> 6` and the next of the copy of `k`, by `7j mod 64`. -/
def window : List Instr :=
  [.shift .sll .d .t0 ctr 3, .sub .t0 .t0 ctr,
   .shift .srl .d .t1 .t0 6, .shift .sll .d .t1 .t1 3, .add .t1 .t1 wb,
   .load .d .t2 .t1 (c.sl KC), .load .d .t3 .t1 (c.sl KC + 8),
   .shiftReg .srl .d .t2 .t2 .t0, .logicImm .xor .t4 .t0 63,
   .shift .sll .d .t3 .t3 1, .shiftReg .sll .d .t3 .t3 .t4,
   .logic .or .t2 .t2 .t3, .logicImm .and .t2 .t2 127]

/-- From the window in `t2`: the digit's sign's mask to `PT`'s first word,
the entry's number `t = |d| - 1` in `t2`, the mask of `|d| = 0` to `PT`'s
second word. -/
def digit : List Instr :=
  [.addi .t2 .t2 (-64), .shift .sra .d .t3 .t2 63, .logic .xor .t2 .t2 .t3, .sub .t2 .t2 .t3,
   .addi .t2 .t2 (-1), .shift .sra .d .t4 .t2 63,
   .store .d .t3 wb (c.sl PT), .store .d .t4 wb (c.sl PT + 8)]

/-- The mask of bit `b` of `t2` into `maskReg b`. -/
def maskOfBit (b : Nat) : List Instr :=
  [.shift .sll .d (maskReg b) .t2 (63 - b), .shift .sra .d (maskReg b) (maskReg b) 63]

/-- The table's row `j` (for `j` in `s1`, the table's address in `s4`): `a0`
and `a7 = a0 + 2048`. -/
def row : List Instr :=
  [.shift .sll .d .t0 ctr 12, .add .a0 .s4 .t0, .addi .a7 .a0 2047, .addi .a7 .a7 1]

/-- The entry: the window, the digit, the masks, the row, the `2 n`
quadwords, then `Z = 1`, and `(0 : 1 : 0)` if `|d| = 0`. -/
def select : List Instr :=
  (window c) ++ (digit c) ++ (List.range 6).flatMap maskOfBit ++ row ++
    (List.range (2 * c.n)).flatMap (scanWord c) ++ copy c.n (c.sl DZ) (c.sl ONEP) ++
    [.load .d .a7 wb (c.sl PT + 8)] ++
    sel c.n (c.sl DX) (c.sl DX) (c.sl ZERO) ++ sel c.n (c.sl DY) (c.sl DY) (c.sl ONEP) ++
    sel c.n (c.sl DZ) (c.sl DZ) (c.sl ZERO)

/-- `y = -y` if the digit is negative, by its sign's mask. -/
def negate : Prog isa :=
  .seq (subCall c.FP (c.sl ACC) (c.sl ZERO) (c.sl DY))
    (.block ([.load .d .a7 wb (c.sl PT)] ++ sel c.n (c.sl DY) (c.sl DY) (c.sl ACC)))

/-- One step: `s1 -= 1`, the signed entry `D`, and `R = R + D`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select c)) <|
  .seq (negate c) <|
  .seq (fprog c.FP (rcb3 c.rcb3Slots (c.pt RX RY RZ) (c.pt DX DY DZ) (c.pt TX TY TZ)))
    (.block (copy c.n (c.sl RX) (c.sl TX) ++ copy c.n (c.sl RY) (c.sl TY) ++ copy c.n (c.sl RZ) (c.sl TZ)))

/-- The comb's body: the copy of `k` and its zero word, `R = S` (`start`,
affine, in Montgomery's form), then the steps. -/
def body (start : Nat × Nat) : Prog isa :=
  .seq (.block (copy c.n (c.sl KC) (c.sl K) ++ [.li .t0 0, .store .d .t0 wb (c.sl KC + 8 * c.n)] ++
    Ecdh.RISCV64.setConst c.n (c.sl RX) (Ecdh.RISCV64.Cfg.mont c start.1) ++
    Ecdh.RISCV64.setConst c.n (c.sl RY) (Ecdh.RISCV64.Cfg.mont c start.2) ++ copy c.n (c.sl RZ) (c.sl ONEP) ++
    [.li ctr J]))
    (.loop (step c) more)

/-- `vg_<curve>_mul_g(ws = a0)`: the table's address (`lla`, first, into
`t0`, then `s4`), `s0`, `s1`, `s4` and `ra` kept around the body, with the
working space's base in `s0`. -/
def combFn (sym : String) (start : Nat × Nat) : Prog isa :=
  .seq (.block [.lla .t0 sym, .store .d .s0 .a0 c.mulSave, .store .d .s1 .a0 (c.mulSave + 8),
    .store .d .ra .a0 (c.mulSave + 16), .store .d .s4 .a0 (c.mulSave + 24), .addi .s0 .a0 0, .addi .s4 .t0 0]) <|
  .seq (body c start) (.block [.load .d .ra .s0 (c.mulSave + 16), .load .d .s4 .s0 (c.mulSave + 24),
    .load .d .s1 .s0 (c.mulSave + 8), .load .d .s0 .s0 c.mulSave])

end Cfg

/-! ## P-256 -/

/-- The table's symbol. -/
def p256Sym : String := "VG_P256_COMB"

/-- The words of P-256's tables (`Impl/P256/CombTable7.lean`), in
Montgomery's form. -/
@[irreducible] def p256CombWords : List (BitVec 64) :=
  tcombWords 4 (2 ^ 256) Spec.P256.curve.p Impl.P256.p256Comb7

def p256CombConsts : List (String × List (BitVec 64)) := [(p256Sym, p256CombWords)]

/-- `vg_p256_mul_g`. -/
def mulGP256 : Prog isa := Cfg.combFn p256 p256Sym Impl.P256.p256Comb7Start

/-- The name of `vg_p256_mul_g`. -/
def mulGP256Name : String := "vg_p256_mul_g"

end VG.Impl.Ecdsa.RISCV64.Comb
