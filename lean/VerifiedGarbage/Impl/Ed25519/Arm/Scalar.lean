module

public import VerifiedGarbage.Impl.Ed25519.Arm.Packed
public import VerifiedGarbage.Impl.Ed25519.Arm.Word
public import VerifiedGarbage.Spec.Ed25519

/-! Scalar arithmetic modulo the Ed25519 subgroup order. All carries use
16-bit limbs and baseline 32-bit instructions.

A 512-bit number `N = N₀ + 2²⁵⁶ N₁`, 32 limbs at `ACC`, is reduced modulo
`L = 2²⁵² + c` with products by the constant `d = 16 c = 16 L - 2²⁵⁶`, of 129
bits, since `2²⁵⁶ ≡ -d`:

* `P₁ = N₁ d` (`SQ1`), so `N ≡ N₀ - P₁`, and `P₂ = (P₁ >> 256) d` (`SQ2`), so
  `-P₁ ≡ -(P₁ mod 2²⁵⁶) + P₂`, and `P₂ < 2²⁵⁷`: `h = P₂ >> 256` is 0 or 1;
* `T = N₀ + (2²⁵⁶ - 1 - P₁ mod 2²⁵⁶) + 1 + P₂ mod 2²⁵⁶ + (1 - h) d`, which is
  `N₀ - P₁ mod 2²⁵⁶ + P₂ mod 2²⁵⁶ - h d + 16 L`, congruent to `N` and below
  `2²⁵⁸`, in `SR` with its carry out;
* `T = l + 2²⁵² q` with `q < 64`, and `U = l + (64 - q) c + (L - 64 c)`, which
  is `l + L - q c`, congruent to `T` and below `2 L`;
* `U - L` if that is not negative.

Each number is the limbs of sixteen sums below `2³²` (`pass`), and a product
is one row of `d`'s 9 limbs for each limb of the number that `d` multiplies. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

/-- The running remainder and the candidate after subtracting L. -/
def SR : Nat := 256
def SD : Nat := 320

/-- The products `N₁ d`, of 25 limbs, and `(N₁ d >> 256) d`, of 18. -/
def SQ1 : Nat := 384
def SQ2 : Nat := 512

/-- The radix-65536 complement of L, without its final carry-in. -/
def scalarComplement (k : Nat) : Nat := 65535 - Spec.Ed25519.L / 2 ^ (16 * k) % 65536

def scalarSubtractSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (SR + 4 * k), .movw .r2 (BitVec.ofNat 16 (scalarComplement k)),
    .dp .add .r3 .r3 (.reg .r2)]

/-- Carry-out r5 is zero exactly when the unreduced scalar in SR is below L. -/
def scalarCompare : List Instr :=
  [.movw .r6 65535, .mov .r5 (.imm 1)] ++ pass .r0 SD scalarSubtractSrc

/-- Limb `j` of `d = 16 L - 2²⁵⁶`, of `c = L - 2²⁵²` and of `L - 64 c`. -/
def scalarD (j : Nat) : Nat := (16 * Spec.Ed25519.L - 2 ^ 256) / 2 ^ (16 * j) % 65536
def scalarC (j : Nat) : Nat := (Spec.Ed25519.L - 2 ^ 252) / 2 ^ (16 * j) % 65536
def scalarE (j : Nat) : Nat := (64 * 2 ^ 252 - 63 * Spec.Ed25519.L) / 2 ^ (16 * j) % 65536

/-- `r3 += r1 · v`, for a limb `v` of a constant. -/
def scalarMla (v : Nat) : List Instr := [.movw .r2 (BitVec.ofNat 16 v), .mla .r3 .r1 .r2 .r3]

/-- `pass`, for the `n` limbs of a shorter number. -/
def passN (n : Nat) (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range n).flatMap fun k => src k ++ Impl.X25519.Arm.carryStep rb (o + 4 * k)

/-- Limb `j` of row `i` (`r7` = the base plus `4 i`, the row's limb in `r1`)
into `r3`: `r1 d_j + acc[i + j]`. -/
def scalarRowSrc (acc j : Nat) : List Instr := [.ldr .r3 .r7 (acc + 4 * j)] ++ scalarMla (scalarD j)

/-- Row `i` of a product by `d`, of 9 limbs: `acc[i, i + 10) = acc[i, i + 9) + x_i · d`. -/
def scalarRow (acc x : Nat) : List Instr :=
  [.ldr .r1 .r7 x, .mov .r5 (.imm 0)] ++ passN 9 .r7 acc (scalarRowSrc acc) ++
    [.str .r5 .r7 (acc + 36), .dp .add .r7 .r7 (.imm 4), .subs .r9 .r9 (.imm 1)]

/-- `acc[0, n + 9) = x[0, n) · d`, with the mask of a limb in `r6`. -/
def scalarMulD (acc x n : Nat) : Prog isa :=
  .seq (.block ([.mov .r3 (.imm 0)] ++ storeN .r3 acc 9 ++
      [.mov .r7 (.reg .r0), .mov .r9 (.imm (BitVec.ofNat 32 n))]))
    (.loop (.block (scalarRow acc x)) .ne)

/-- Limb `k` of `T`, with `1 - h` in `r1`. -/
def scalarSumSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (ACC + 4 * k), .dp .add .r3 .r3 (.reg .r6), .ldr .r2 .r0 (SQ1 + 4 * k),
    .dp .sub .r3 .r3 (.reg .r2), .ldr .r2 .r0 (SQ2 + 4 * k), .dp .add .r3 .r3 (.reg .r2)] ++
    (if k < 9 then scalarMla (scalarD k) else [])

/-- `T` into `SR`, its carry out in `r5`. -/
def scalarSum : List Instr :=
  [.ldr .r2 .r0 (SQ2 + 64), .mov .r1 (.imm 1), .dp .sub .r1 .r1 (.reg .r2), .mov .r5 (.imm 1)] ++
    pass .r0 SR scalarSumSrc

/-- `64 - q` into `r1`, for `q = T >> 252`, and `T mod 2²⁵²` left in `SR`. -/
def scalarTop : List Instr :=
  [.ldr .r3 .r0 (SR + 60), .mov .r2 (.shifted .r3 .lsr 12),
    .dp .add .r2 .r2 (.shifted .r5 .lsl 4), .mov .r1 (.imm 64), .dp .sub .r1 .r1 (.reg .r2),
    .mov .r3 (.shifted .r3 .lsl 20), .mov .r3 (.shifted .r3 .lsr 20), .str .r3 .r0 (SR + 60),
    .mov .r5 (.imm 0)]

/-- Limb `k` of `U`, with `64 - q` in `r1`. -/
def scalarLowSrc (k : Nat) : List Instr :=
  [.ldr .r3 .r0 (SR + 4 * k)] ++ (if k < 8 then scalarMla (scalarC k) else []) ++
    [.movw .r2 (BitVec.ofNat 16 (scalarE k)), .dp .add .r3 .r3 (.reg .r2)]

/-- `SR` less `L`, if that is not negative, for a number below `2 L`. -/
def scalarCondSub : List Instr :=
  [.mov .r5 (.imm 1)] ++ pass .r0 SD scalarSubtractSrc ++
    [.mov .r9 (.imm 0), .dp .sub .r9 .r9 (.reg .r5)] ++ cswap SR SD

/-- The 32 limbs at `ACC` modulo `L`, into `SR`. -/
def scalarFold : Prog isa :=
  .seq (.block [.movw .r6 65535]) <| .seq (scalarMulD SQ1 (ACC + 64) 16) <|
    .seq (scalarMulD SQ2 (SQ1 + 64) 9) <|
      .block (scalarSum ++ scalarTop ++ pass .r0 SR scalarLowSrc ++ scalarCondSub)

/-- Read the complete 64-byte integer from r12. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block (unpackField ACC 0 ++ unpackField (ACC + 64) 32)) scalarFold

/-- Exact 256-by-256 multiplication, before any modular reduction. -/
def scalarWideMul (x y : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 16)]))
    (.loop (.block (row x y)) .ne)

end VG.Impl.Ed25519.Arm
