module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide

/-!
# Multiplication modulo an odd modulus of eight words, as functions, on RISC-V

`vg_<name>_mul_mod_<m>` for an eight-word modulus known when the code is
generated, as `GenWide`'s, whose entry, copies and layout (from
`a3 = ws + 6144`) these functions have, but on the pointers (`fast`) the
running value is in registers:

1. `s6`–`s11` are kept at `SV` (`save`);
2. the product's sixteen words, at `SQ`: of `[t4]` and `[t5]` by rows
   (`mulProd`), or, when the pointers are equal, the square (`sqrProd`): the
   products `aᵢ aⱼ`, `i < j`, by rows, then GenWide's doubling with the
   squares added (`diag`). A row's eight words are in `VR`, and its carry in
   `C`; the operand's words are in registers (`AR`) but the last ones, which
   are loaded at each use (`opA`);
3. Montgomery's reduction of the product (`red`), separated operand scanning:
   the window of eight words in `VR`, the modulus's words in `AR` but the
   last, loaded at each use (`opM`); round `i`'s quotient word replaces word
   `i` in its register, which word `i + 8` then takes;
4. the final subtraction (`csub`): the window less the modulus, at `D`, and
   that or the window by a mask, into `[t2]`;
5. `s6`–`s11` back (`restore`).

A step of a row multiplies once by `mul` and once by `mulhu`; every selection
is a mask, and the only branches are on the pointers, which are public, as
every address is a pointer plus a constant.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Wide8

open VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv T N SQ diag fnWith fnA mulCore)
open VG.Impl.Words.RISCV64 (li64)

/-! ## Registers and layout -/

/-- The carry word of a row, and the two words of a product. -/
abbrev C : Reg := .t3
abbrev LO : Reg := .t6
abbrev HI : Reg := .s6

/-- The word of the second operand a row multiplies by. -/
abbrev Y : Reg := .a6

/-- The carry out of the window, in the reduction. -/
abbrev TOP : Reg := .t4

def VL : List Reg := [.t0, .t1, .a7, .s7, .s8, .s9, .s10, .s11]

/-- The register of word `i` of the running value. -/
def VR (i : Nat) : Reg := VL.getD (i % 8) .t0

def AL : List Reg := [.a0, .a1, .a2, .a4, .a5, .a6, .t5]

/-- The register of word `j < 7` of an operand or of the modulus. -/
def AR (j : Nat) : Reg := AL.getD j .a0

/-- The registers kept. -/
def KR : List Reg := [.s6, .s7, .s8, .s9, .s10, .s11]

/-- `s6`–`s11`, the modulus's last word, its `m'`, and the difference. -/
abbrev SV : Nat := T 8
abbrev M7 : Nat := T 8 + 48
abbrev NI : Nat := T 8 + 56
abbrev D : Nat := N 8

/-- The product's word `j`. -/
abbrev P (j : Nat) : Nat := SQ 8 + 8 * j

def save : List Instr := (List.range 6).flatMap fun j => [.store .d (KR.getD j .s6) .a3 (SV + 8 * j)]

def restore : List Instr := (List.range 6).flatMap fun j => [.load .d (KR.getD j .s6) .a3 (SV + 8 * j)]

/-! ## Rows -/

/-- `v + 2⁶⁴ C := x y + v + C`, or without `v` (`acc` false), for `x` that may be `HI`. -/
def mac (acc : Bool) (x y v : Reg) : List Instr :=
  if acc then
    [.mul LO x y, .mulhu HI x y, .add v v LO, .sltu LO v LO, .add HI HI LO, .add v v C, .sltu LO v C,
      .add C HI LO]
  else [.mul v x y, .mulhu HI x y, .add v v C, .sltu LO v C, .add C HI LO]

/-- `mac` without the carry in. -/
def mac1 (acc : Bool) (x y v : Reg) : List Instr :=
  if acc then [.mul LO x y, .mulhu C x y, .add v v LO, .sltu LO v LO, .add C C LO]
  else [.mul v x y, .mulhu C x y]

/-- An operand's word: the code that loads it, and its register. -/
abbrev Op := List Instr × Reg

/-- Word `j` of `[t4]`, the first `n` in registers. -/
def opA (n j : Nat) : Op := if j < n then ([], AR j) else ([.load .d HI .t4 (8 * j)], HI)

/-- Word `j` of the modulus. -/
def opM (j : Nat) : Op := if j < 7 then ([], AR j) else ([.load .d HI .a3 M7], HI)

/-- The words `VR i …` plus `y` times the operand's `n` words, with the carry `C` in and out. -/
def row (acc : Bool) (f : Nat → Op) (y : Reg) (i n : Nat) : List Instr :=
  (List.range n).flatMap fun j => (f j).1 ++ mac acc (f j).2 y (VR (i + j))

/-- `row` of `n + 1` words without the carry in. -/
def row1 (acc : Bool) (f : Nat → Op) (y : Reg) (i n : Nat) : List Instr :=
  (f 0).1 ++ mac1 acc (f 0).2 y (VR i) ++ row acc (fun j => f (j + 1)) y (i + 1) n

/-! ## The products -/

/-- The first `n` words of `[t4]` into `AR`. -/
def loadA (n : Nat) : List Instr := (List.range n).flatMap fun j => [.load .d (AR j) .t4 (8 * j)]

/-- Row `i` of the product: its low word stored. -/
def mulRow (i : Nat) : List Instr :=
  [.load .d Y .t5 (8 * i)] ++ row1 (decide (0 < i)) (opA 5) Y i 7 ++
    [.store .d (VR i) .a3 (P i), .addi (VR i) C 0]

/-- The product of `[t4]` and `[t5]`. -/
def mulProd : List Instr :=
  loadA 5 ++ (List.range 8).flatMap mulRow ++ (List.range 8).flatMap fun j => [.store .d (VR (8 + j)) .a3 (P (8 + j))]

/-- Row `i` of the square's products `aᵢ aⱼ`, `i < j`: its two low words stored. -/
def sqrRow (i : Nat) : List Instr :=
  row1 (decide (0 < i)) (fun j => opA 7 (i + 1 + j)) (AR i) (2 * i + 1) (6 - i) ++
    [.addi (VR (i + 8)) C 0, .store .d (VR (2 * i + 1)) .a3 (P (2 * i + 1)),
      .store .d (VR (2 * i + 2)) .a3 (P (2 * i + 2))]

/-- The square of `[t4]`. -/
def sqrProd : List Instr :=
  loadA 7 ++ (List.range 7).flatMap sqrRow ++
    [.li .a2 0, .store .d .a2 .a3 (P 0), .store .d .a2 .a3 (P 15), .li .a5 0] ++ (List.range 8).flatMap (diag 8)

/-! ## The reduction -/

variable (m : Nat)

/-- The modulus's words and `m'`. -/
def consts : List Instr :=
  ((List.range 7).flatMap fun j => li64 (AR j) LO (wordOf m j)) ++ (li64 HI LO (wordOf m 7) ++
    ([.store .d HI .a3 M7] : List Instr)) ++ (li64 HI LO (BitVec.ofNat 64 (negInv m)) ++ ([.store .d HI .a3 NI] : List Instr))

/-- The quotient word of `VR i`, in place, and the carry word of adding its
product with the modulus's word 0, in `C`. -/
def quot (i : Nat) : List Instr :=
  [.load .d LO .a3 NI, .mul (VR i) (VR i) LO, .mulhu C (VR i) (AR 0), .li LO 0, .sltu LO LO (VR i), .add C C LO]

/-- Word `i + 8` of the product plus the carries `C` and `TOP`, into `VR i`, the carry out in `TOP`. -/
def top (i : Nat) : List Instr :=
  [.load .d (VR i) .a3 (P (8 + i)), .add (VR i) (VR i) C, .sltu LO (VR i) C, .add (VR i) (VR i) TOP,
    .sltu TOP (VR i) TOP, .add TOP TOP LO]

/-- Round `i`. -/
def redRound (i : Nat) : List Instr := quot i ++ row true (fun j => opM (j + 1)) (VR i) (i + 1) 7 ++ top i

/-- The product reduced, into `VR 0`–`VR 7` and `TOP`. -/
def red : List Instr :=
  ((List.range 8).flatMap fun j => [.load .d (VR j) .a3 (P j)]) ++ [.li TOP 0] ++ (List.range 8).flatMap redRound

/-! ## The final subtraction -/

/-- The register the subtraction has the modulus's word `j` in, the last one loaded. -/
def MR (j : Nat) : Reg := if j < 7 then AR j else .a0

/-- Word `j` of the window less the modulus, with the borrow in `C`, at `D`. -/
def subStep (j : Nat) : List Instr :=
  (if j < 7 then [] else [.load .d .a0 .a3 M7]) ++
    ([.sltu LO (VR j) (MR j), .sub HI (VR j) (MR j), .sltu (MR j) HI C, .sub HI HI C, .add C LO (MR j),
      .store .d HI .a3 (D + 8 * j)] : List Instr)

/-- Word `j` of the result: the difference's, or the window's under the mask `TOP`. -/
def selStep (j : Nat) : List Instr :=
  [.load .d LO .a3 (D + 8 * j), .logic .xor HI (VR j) LO, .logic .and HI HI TOP, .logic .xor LO LO HI,
    .store .d LO .t2 (8 * j)]

/-- The window and `TOP`, below twice the modulus, reduced into `[t2]`. -/
def csub : List Instr :=
  [.li C 0] ++ (List.range 8).flatMap subStep ++ [.sub TOP TOP C] ++ (List.range 8).flatMap selStep

/-! ## The functions -/

/-- `[t2] = [t4] [t5] R⁻¹ mod m`. -/
def fast : Prog isa :=
  .seq (.block save) <| .seq (.ite (.eq .t4 .t5) (.block sqrProd) (.block mulProd)) <|
    .block (consts m ++ (red ++ (csub ++ restore)))

/-- The function multiplying modulo `m`. -/
def mulFn : Prog isa := fnWith 8 (fast m) (mulCore 8 m)

/-- The function multiplying modulo `m`, for aligned offsets. -/
def mulFnA : Prog isa := fnA (fast m)

end VG.Impl.Weierstrass.RISCV64.Wide8
