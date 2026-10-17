module

public import VerifiedGarbage.Impl.Mont.Arm.Dynamic

/-!
# A runtime Montgomery workspace and exponentiation on 32-bit ARM

The working space (base `r12`) holds a header of 256 bytes, `m'` at `[0]`
and the exponentiation's selection mask at `[4]` (the rest is its user's),
then slots of `8n + 8`
bytes: the modulus, the subtraction temporary, the accumulator (four slots,
for its `2D + 2` digits), one, `R²`, the base, the result, the conditional
product and the exponent. All offsets depend only on the public width.

The counts of the doublings and of the exponent's bits are in `lr`, which
the arithmetic leaves alone.
-/

@[expose] public section

namespace VG.Impl.Mont.Arm.Dynamic

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm

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

def contextBytes (n : Nat) : Nat := slot n 12

/-- `m'` and the selection mask, in the header. -/
def invO : Nat := 0
def maskO : Nat := 4

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

/-- The inverse, one and `R² mod m`, for the modulus at `[modS n]`. -/
def contextSetup (n : Nat) : Prog isa :=
  .seq (.block (setupInverse (modS n))) <| .seq (one n (oneS n))
    (powerTwo (contextMod n) (accS n) (rrS n) (128 * n))

/-! ## Exponentiation -/

/-- `[mask]` all ones if the exponent's low bit is set, else zero. -/
def exponentMask (n : Nat) : List Instr :=
  ptr .r1 (expS n) ++ [.ldr .r3 .r1 0, .dp .and .r3 .r3 (.imm 1), .mov .r4 (.imm 0),
    .dp .sub .r3 .r4 (.reg .r3), .str .r3 .r12 maskO]

/-- The exponent's `k` words shifted down a bit, word `j` through `r1`. -/
def shiftWords : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, j =>
    [.ldr .r4 .r1 (4 * j), .mov .r4 (.shifted .r4 .lsr 1)] ++
    (if k = 0 then [] else [.ldr .r5 .r1 (4 * j + 4), .mov .r5 (.shifted .r5 .lsl 31),
      .dp .orr .r4 .r4 (.reg .r5)]) ++
    [.str .r4 .r1 (4 * j)] ++ shiftWords k (j + 1)

def shiftExponent (n expWords : Nat) : List Instr := ptr .r1 (expS n) ++ shiftWords expWords 0

/-- The result times the base, kept where the mask is all ones. -/
def exponentProduct (n : Nat) : Prog isa :=
  .seq (.block (exponentMask n)) <|
  .seq (mul (contextMod n) invO (accS n) (prodS n) (resS n) (baseS n))
    (.seq (.block [.ldr .r3 .r12 maskO]) (selectW (2 * n) (resS n) (prodS n) (resS n)))

def exponentBody (n expWords : Nat) : Prog isa :=
  .seq (exponentProduct n) <|
  .seq (mul (contextMod n) invO (accS n) (baseS n) (baseS n) (baseS n)) (.block (shiftExponent n expWords))

def exponentStep (n expWords : Nat) : Prog isa :=
  .seq (exponentBody n expWords) (.block [.subs .lr .lr (.imm 1)])

/-- `[resS] = [baseS]^[expS] mod m`, the exponent `expWords` words, with a
public number of iterations; the base and the exponent are consumed. -/
def exponentiate (n expWords : Nat) : Prog isa :=
  .seq (mul (contextMod n) invO (accS n) (resS n) (rrS n) (oneS n)) <|
  .seq (mul (contextMod n) invO (accS n) (baseS n) (baseS n) (rrS n)) <|
  .seq (.block [.movw .lr (BitVec.ofNat 16 (32 * expWords))]) <|
  .seq (.loop (exponentStep n expWords) .ne)
    (mul (contextMod n) invO (accS n) (resS n) (resS n) (oneS n))

end VG.Impl.Mont.Arm.Dynamic
