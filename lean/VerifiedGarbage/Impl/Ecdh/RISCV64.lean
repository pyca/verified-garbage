module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64

/-!
# The check of a public point on RISC-V

`vg_<curve>_check_point(ws)` (`Spec/Weierstrass/CheckPoint.lean`), for a
curve of `n` 64-bit words, on the layout of `Impl/Ecdsa/RISCV64.lean`:

1. `s0` and `ra` saved in slot 2 (the function's own working space), and
   the working space's base to `s0`;
2. the masks of `x < p` and `y < p` into the flag (`ltMask`: `x - p` word
   by word with borrows, whose last borrow is set if and only if `x < p`);
3. `x R mod p` and `y R mod p`, by multiplications by `R² mod p`, and
   `y² - (x³ + a x + b)` in Montgomery's form (`curveOps`), whose mask of
   being zero (`zeroMask`) goes into the flag;
4. the point the scalar multiplication takes: the public point's
   coordinates in Montgomery's form if the flag is set, else `G`'s, by the
   flag as a mask;
5. `ra` and `s0` restored.

Every address is `s0` plus a constant, and the only branches are in the
field functions, on their pointers: the function is constant time.
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64

/-! Slots of the check (`Spec/Weierstrass/CheckPoint.lean`). -/
def CX := 33
def CXM := 34
def CYM := 35
def CY := 36
def W0 := 37
def CPX := 38
def R2P := 39
def BP := 40
def W1 := 41
def W2 := 42
def CPY := 43
def FLAG := 44

/-- Word `j` of `[a] - [m]` with the borrow in `t5` (into and out of it),
through `t3`, `t4`, `t6` and `a4`. -/
def ltWord (a m : Nat) : List Instr :=
  [.load .d .t3 wb a, .load .d .t4 wb m,
    .sltu .t6 .t3 .t4, .sub .t3 .t3 .t4, .sltu .a4 .t3 .t5, .sub .t3 .t3 .t5, .add .t5 .t6 .a4]

/-- The words of `[a] - [m]`, `k` of them, the borrow in `t5`. -/
def ltWords : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, a, m => ltWord a m ++ ltWords k (a + 8) (m + 8)

/-- The mask `a7` of `[a] < [m]` (all ones if it is), `n` words: the borrow out
of `[a] - [m]`, negated. -/
def ltMask (n a m : Nat) : List Instr :=
  [.li .t5 0] ++ ltWords n a m ++ [.li .t6 0, .sub .a7 .t6 .t5]

/-- The words of `[a]` or'ed into `t3`, through `t4`. -/
def orWords : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, a => [.load .d .t4 wb a, .logic .or .t3 .t3 .t4] ++ orWords k (a + 8)

/-- The mask `a7` of `[a] = 0` (all ones if it is), `n` words: the words
or'ed, the top bit of `x | -x` (set iff `x ≠ 0`), less one. -/
def zeroMask (n a : Nat) : List Instr :=
  [.li .t3 0] ++ orWords n a ++
    [.li .t4 0, .sub .t4 .t4 .t3, .logic .or .t4 .t4 .t3, .shift .srl .d .t4 .t4 63, .addi .a7 .t4 (-1)]

namespace Cfg

variable (c : Cfg)

/-- The flag `&=` the mask `a7`, through `t0`. -/
def andFlag : List Instr :=
  [.load .d .t0 wb (c.sl FLAG), .logic .and .t0 .t0 .a7, .store .d .t0 wb (c.sl FLAG)]

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl CYM) (c.sl CYM), .mul (c.sl W1) (c.sl CXM) (c.sl CXM),
    .mul (c.sl W2) (c.sl W1) (c.sl CXM), .mul (c.sl W1) (c.sl AP) (c.sl CXM),
    .add (c.sl CPX) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl CPX) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- Where `vg_<curve>_check_point` keeps `s0` and `ra`: slot 2. -/
def checkSave : Nat := c.sl TMP

/-- `vg_<curve>_check_point(ws = a0)`. -/
def checkFn : Prog isa :=
  .seq (.block [.store .d .s0 .a0 (checkSave c), .store .d .ra .a0 (checkSave c + 8), .addi .s0 .a0 0]) <|
  .seq (.block (ltMask c.n (c.sl CX) (c.sl MP) ++ andFlag c ++ ltMask c.n (c.sl CY) (c.sl MP) ++ andFlag c)) <|
  .seq (mulCall c.FP (c.sl CXM) (c.sl CX) (c.sl R2P)) <|
  .seq (mulCall c.FP (c.sl CYM) (c.sl CY) (c.sl R2P)) <|
  .seq (fprog c.FP (curveOps c)) <|
  .block (zeroMask c.n (c.sl W1) ++ andFlag c ++ [.load .d .a7 wb (c.sl FLAG)] ++
    sel c.n (c.sl CPX) (c.sl GX) (c.sl CXM) ++ sel c.n (c.sl CPY) (c.sl GY) (c.sl CYM) ++
    [.load .d .ra .s0 (checkSave c + 8), .load .d .s0 .s0 (checkSave c)])

end Cfg

end VG.Impl.Ecdh.RISCV64
