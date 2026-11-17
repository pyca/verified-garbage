module

public import VerifiedGarbage.Impl.Mont.Arm.Dynamic

/-!
# A runtime Montgomery workspace and exponentiation on 32-bit ARM

The working space (base `r12`) holds a header of 256 bytes, `m'` at `[0]`
(the rest is its user's), then slots of `8n + 8`
bytes: the modulus, the subtraction temporary, the accumulator (four slots,
for its `2D + 2` digits), one, `R²`, the base, the result, a product (the
exponentiation's chosen power), the exponent, the sixteen powers of the
exponentiation's table, and the second base and exponent of a product of two
powers. All offsets depend only on the public width.

The counts of the doublings and of the exponent's windows are in `lr`, and
the table's next entry and the count of a window's squarings in `r11`: the
arithmetic leaves both alone.
-/

@[expose] public section

namespace VG.Impl.Mont.Arm.Dynamic

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm

variable (umaal : Bool)

/-- The slots' stride: a number and its top word. -/
def stride (n : Nat) : Nat := 8 * n + 8

def slot (n i : Nat) : Nat := 256 + i * stride n

def modS (n : Nat) : Nat := slot n 0
def tmpS (n : Nat) : Nat := slot n 1
def accS (n : Nat) : Nat := slot n 2
def oneS (n : Nat) : Nat := slot n 6
def rrS (n : Nat) : Nat := slot n 7
def baseS (n : Nat) : Nat := slot n 8
def resS (n : Nat) : Nat := slot n 9
def prodS (n : Nat) : Nat := slot n 10
def expS (n : Nat) : Nat := slot n 11

/-- Entry `j` of the exponentiation's table: the base to the power `j`. -/
def tabS (n j : Nat) : Nat := slot n (12 + j)

/-- The second base and exponent of a product of two powers. -/
def base2S (n : Nat) : Nat := slot n 28
def exp2S (n : Nat) : Nat := slot n 29

def contextBytes (n : Nat) : Nat := slot n 30

/-- `m'`, in the header. -/
def invO : Nat := 0

def contextMod (n : Nat) : Mod := { n, mo := modS n, tmp := tmpS n, minv := 0 }

/-! ## Constants -/

/-- `x := x (2 - m x)`, with `m` in `r5` and `x` in `r7`. -/
def newton : List Instr :=
  [.mul .r4 .r5 .r7, .movw .r2 2, .dp .sub .r4 .r2 (.reg .r4), .mul .r7 .r7 .r4]

/-- `[inv] = -m⁻¹ mod 2¹⁶` for the odd modulus at `[mo]`: from `x = m`, right
modulo 8, three Newton steps give 24 bits. -/
def setupInverse (mo : Nat) : List Instr :=
  ptr .r1 mo ++ [.ldr .r5 .r1 0, mask16, .dp .and .r5 .r5 (.reg .r6), .mov .r7 (.reg .r5)] ++
    newton ++ newton ++ newton ++
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r7), .dp .and .r4 .r4 (.reg .r6), .str .r4 .r12 invO]

/-- `[out] = 1`, `n` 64-bit words. -/
def one (n out : Nat) : Prog isa :=
  .seq (zeros (2 * n) out) (.block (ptr .r10 out ++ [.mov .r4 (.imm 1), .str .r4 .r10 0]))

/-- `2^bits mod m` at `[out]`, for public positive `bits` below `2¹⁶` and
`m > 1`: doublings of one, counted in `lr`. -/
def powerTwo (M : Mod) (acc out bits : Nat) : Prog isa :=
  .seq (one M.n out) <| .seq (.block [.movw .lr (BitVec.ofNat 16 bits)])
    (.loop (.seq (addD M acc out out out) (.block [.subs .lr .lr (.imm 1)])) .ne)

/-- The Montgomery squarings that take `2ⁿ R` to `R²`: each squares the
power of two beside `R`, and `n · 2⁶ = 64 n`. -/
def squarings : Nat := 6

/-- `R² mod m` at `[rrS n]`, `R = 2^(64 n)`: `2^(65 n) = 2ⁿ R` by doublings,
then `squarings` Montgomery squarings, counted in `lr`. -/
def rSquared (n : Nat) : Prog isa :=
  .seq (powerTwo (contextMod n) (accS n) (rrS n) (65 * n)) <|
  .seq (.block [.mov .lr (.imm (BitVec.ofNat 32 squarings))])
    (.loop (.seq (mul umaal (contextMod n) invO (accS n) (rrS n) (rrS n) (rrS n))
      (.block [.subs .lr .lr (.imm 1)])) .ne)

/-- The inverse, one and `R² mod m`, for the modulus at `[modS n]`. -/
def contextSetup (n : Nat) : Prog isa :=
  .seq (.block (setupInverse (modS n))) <| .seq (one n (oneS n)) (rSquared umaal n)

/-! ## Exponentiation

By windows of four bits, from the exponent's top: a table of the base's
sixteen powers, then for each window four squarings and a multiplication by
the window's power, which a scan of the whole table chooses under masks. -/

/-- `r3` all ones if `x = j`, else zero, for `x` and `j` below `2³¹`; and `r4 = 0`. -/
def maskEq (x : Reg) (j : Nat) : List Instr :=
  [.dp .eor .r3 x (.imm (BitVec.ofNat 32 j)), .dp .sub .r3 .r3 (.imm 1), .mov .r3 (.shifted .r3 .lsr 31),
    .mov .r4 (.imm 0), .dp .sub .r3 .r4 (.reg .r3)]

/-- `[prodS]` becomes the table's entry `j` if `r2 = j`. -/
def pick (n j : Nat) : Prog isa :=
  .seq (.block (maskEq .r2 j)) (selectW (2 * n) (prodS n) (tabS n j) (prodS n))

/-- `pick` for the `k` entries from `j`. -/
def scanFrom (n : Nat) : Nat → Nat → Prog isa
  | 0, _ => .block []
  | k + 1, j => .seq (pick n j) (scanFrom n k (j + 1))

/-- `[prodS]` becomes the table's entry `r2`, below 16: every entry is read. -/
def scan (n : Nat) : Prog isa := scanFrom n 16 0

/-- The `k` words from word `j` at `[r1]` shifted up four bits: the bits that
come in, and then those that go out, in `r2`. -/
def shiftUp : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, j =>
    [.ldr .r4 .r1 (4 * j), .dp .orr .r5 .r2 (.shifted .r4 .lsl 4), .mov .r2 (.shifted .r4 .lsr 28),
      .str .r5 .r1 (4 * j)] ++ shiftUp k (j + 1)

/-- The exponent's top four bits into `r2`, and the exponent shifted up by them. -/
def window (n expWords : Nat) : List Instr :=
  ptr .r1 (expS n) ++ (.mov .r2 (.imm 0) :: shiftUp expWords 0)

/-- The `k` words at `[src]` to `[r11]`, which moves past them. -/
def copyOut (k src : Nat) : Prog isa :=
  .seq (.block (ptr .r10 src ++ ptr .r9 (src + 4 * k)))
    (ptrLoop .r10 [.ldr .r5 .r10 0, .str .r5 .r11 0, bump .r10 4, bump .r11 4])

/-- An entry of the table, the power in `[prodS]`, and the next power. -/
def tableStep (n : Nat) : Prog isa :=
  .seq (copyOut (2 * n) (prodS n)) <|
  .seq (mul umaal (contextMod n) invO (accS n) (prodS n) (prodS n) (baseS n))
    (.block [bump .r11 8, .subs .lr .lr (.imm 1)])

/-- The table: the sixteen powers of the base, which is encoded. -/
def table (n : Nat) : Prog isa :=
  .seq (mul umaal (contextMod n) invO (accS n) (prodS n) (rrS n) (oneS n)) <|
  .seq (mul umaal (contextMod n) invO (accS n) (baseS n) (baseS n) (rrS n)) <|
  .seq (.block (ptr .r11 (tabS n 0) ++ [.mov .lr (.imm 16)])) (.loop (tableStep umaal n) .ne)

/-- The result squared four times, counted in `r11`. -/
def squareFour (n : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.imm 4)])
    (.loop (.seq (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (resS n))
      (.block [.subs .r11 .r11 (.imm 1)])) .ne)

/-- A window: the result to the sixteenth power, times the window's power. -/
def windowStep (n expWords : Nat) : Prog isa :=
  .seq (squareFour umaal n) <|
  .seq (.block (window n expWords)) <|
  .seq (scan n) <|
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (prodS n))
    (.block [.subs .lr .lr (.imm 1)])

/-- `[resS] = [baseS]^[expS] mod m`, the exponent `expWords` words, with a
public number of iterations; the base and the exponent are consumed. -/
def exponentiate (n expWords : Nat) : Prog isa :=
  .seq (table umaal n) <|
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (rrS n) (oneS n)) <|
  .seq (.block [.movw .lr (BitVec.ofNat 16 (8 * expWords))]) <|
  .seq (.loop (windowStep umaal n expWords) .ne)
    (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (oneS n))

/-! ## A product of two powers

`[baseS]^[expS] · [base2S]^[exp2S]` in one pass over both exponents, two bits
of each at a time: the table's entry `4 i + j` is the second base to the
power `i` times the first to the power `j`, and each window is two squarings
and a multiplication by the entry the two exponents' top two bits choose. -/

/-- As `shiftUp`, by two bits. -/
def shiftUp2 : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, j =>
    [.ldr .r4 .r1 (4 * j), .dp .orr .r5 .r2 (.shifted .r4 .lsl 2), .mov .r2 (.shifted .r4 .lsr 30),
      .str .r5 .r1 (4 * j)] ++ shiftUp2 k (j + 1)

/-- The top two bits of the exponent at `[E]` into `r2`, and the exponent shifted up by them. -/
def windowTwo (E expWords : Nat) : List Instr := ptr .r1 E ++ (.mov .r2 (.imm 0) :: shiftUp2 expWords 0)

/-- `r2 = 4 i + j`, for the top two bits `i` of the second exponent and `j` of
the first, which are shifted out. -/
def window2 (n expWords : Nat) : Prog isa :=
  .seq (.block (windowTwo (exp2S n) expWords)) <|
  .seq (.block [.mov .r6 (.shifted .r2 .lsl 2)]) <|
  .seq (.block (windowTwo (expS n) expWords)) (.block [.dp .orr .r2 .r2 (.reg .r6)])

/-- The table's entries that are products of two others: `(k, a, b)` for
entry `k`, the product of entries `a` and `b`. -/
def tableOps : List (Nat × Nat × Nat) :=
  [(2, 1, 1), (3, 2, 1), (5, 4, 1), (6, 4, 2), (7, 4, 3), (8, 4, 4), (9, 8, 1), (10, 8, 2), (11, 8, 3),
    (12, 8, 4), (13, 12, 1), (14, 12, 2), (15, 12, 3)]

def tableFill (n : Nat) : List (Nat × Nat × Nat) → Prog isa
  | [] => .block []
  | (k, a, b) :: r =>
    .seq (mul umaal (contextMod n) invO (accS n) (tabS n k) (tabS n a) (tabS n b)) (tableFill n r)

/-- The table of a product of two powers: one, the two bases, encoded, and
their products. -/
def table2 (n : Nat) : Prog isa :=
  .seq (mul umaal (contextMod n) invO (accS n) (tabS n 0) (rrS n) (oneS n)) <|
  .seq (mul umaal (contextMod n) invO (accS n) (tabS n 1) (baseS n) (rrS n)) <|
  .seq (mul umaal (contextMod n) invO (accS n) (tabS n 4) (base2S n) (rrS n)) (tableFill umaal n tableOps)

/-- A window of both exponents: the result to its fourth power, times the
table's entry for their top two bits. -/
def windowStep2 (n expWords : Nat) : Prog isa :=
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (resS n)) <|
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (resS n)) <|
  .seq (window2 n expWords) <|
  .seq (scan n) <|
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (prodS n))
    (.block [.subs .lr .lr (.imm 1)])

/-- `[resS] = [baseS]^[expS] · [base2S]^[exp2S] mod m`, the exponents
`expWords` words each, with a public number of iterations; the exponents are
consumed. -/
def exponentiate2 (n expWords : Nat) : Prog isa :=
  .seq (table2 umaal n) <|
  .seq (mul umaal (contextMod n) invO (accS n) (resS n) (rrS n) (oneS n)) <|
  .seq (.block [.movw .lr (BitVec.ofNat 16 (16 * expWords))]) <|
  .seq (.loop (windowStep2 umaal n expWords) .ne)
    (mul umaal (contextMod n) invO (accS n) (resS n) (resS n) (oneS n))

end VG.Impl.Mont.Arm.Dynamic
