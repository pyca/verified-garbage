module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: the arithmetic of polynomials

As ML-KEM's on RISC-V (`Impl/MlKem/RISCV64/Ntt.lean`), for
`q = 8380417 = 2²³ − 2¹³ + 1`: the coefficients are `u32`s, loaded
zero-extended (`lwu`) and stored as the low word (`sw`), and the arithmetic
is on all 64 bits.

Multiplications are what the code counts, as ML-KEM's does. A product of two
reduced values (or that plus a reduced value) `x` is reduced by Barrett's
method with `mulhu`: `t = ⌊x · m / 2⁶⁴⌋` for `m = ⌊2⁶⁴ / q⌋` is `⌊x / q⌋` or
one less, so `x - t·q` is less than `2q` and congruent to `x`; as
`q = 2²³ − 2¹³ + 1`, the product `t·q` is two shifts, an addition and two
subtractions, and a subtraction of `q` and a `fixup`
(`Impl/MlKem/RISCV64/Poly.lean`) finish it (`reduce`). A reduction thus
multiplies once (against three folds of `x` by `2²³ ≡ 2¹³ − 1`, multiplying
none, but with ten more instructions), so a butterfly multiplies twice, and a
coefficient of `multiplyNTT` twice.
`a5 = m` and `a6 = q` throughout (`consts`).

The tables of the 256 zetas `ζ^BitRev8(m) mod q` (`zetaTab`) and of their
negations (`negZetaTab`, the `z` of Algorithm 42) are stored in `scratch`,
as 256 `u32`s (`table`: each entry a `lui` and an `addi`, then a store,
through `t2`), and read in order through a pointer. The functions use only
registers the calling convention lets them clobber, make no calls and use
no stack.

* `vg_mldsa_ntt(f = a0, scratch = a1)`: the eight layers of Algorithm 41 as
  ML-KEM's seven, with `a0 = f + 1024`, `a7 = 4 len` (from 512, halved,
  until it is 4) and the zetas read from `m = 1` up.
* `vg_mldsa_inv_ntt(f = a0, scratch = a1)`: the eight layers of Algorithm
  42, with `a7` from 4 (doubled, until it is 1024), the negated zetas read
  from `m = 255` down, and the inverse butterflies; then every coefficient
  times `8347681 = 256⁻¹ mod q`.
* `vg_mldsa_multiply_ntt(h = a0, f = a1, g = a2)`: `h[i] = f[i] · g[i]`,
  reduced, counted by `t1`; `vg_mldsa_multiply_add_ntt` adds `h[i]` to the
  product before reducing it.
* `vg_mldsa_add(f = a0, g = a1)`, `vg_mldsa_sub(f = a0, g = a1)`: ML-KEM's
  loops (`Impl.MlKem.RISCV64.addBody`, `subBody`) with `q` in `a5`.

Every address is a pointer plus a constant, and every branch depends on a
counter or a pointer: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Arith

open VG.RISCV64
open VG.Impl.MlKem.RISCV64 (fixup addBody subBody)

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- The `lui` immediate of `v < 2³¹`: `v` rounded to a multiple of 4096. -/
def hi20 (v : Nat) : Nat := (v + 2048) / 4096

/-- `r ← v` for `v < 2³¹ − 2048`: `lui` of `hi20 v`, then `addi` of the rest
(in `[-2048, 2048)`). -/
def loadImm (r : Reg) (v : Nat) : List Instr :=
  [.lui r (BitVec.ofNat 20 (hi20 v)), .addi r r ((v : Int) - 4096 * hi20 v)]

/-- `r ← m = ⌊2⁶⁴ / q⌋ = 2201172575745 = 537395648 · 2¹² + 1537`. -/
def loadM (r : Reg) : List Instr := loadImm r 537395648 ++ [.shift .sll .d r r 12, .addi r r 1537]

/-- `a5 = m`, `a6 = q`. -/
def consts : List Instr := loadM .a5 ++ loadImm .a6 8380417

/-- `d ← d mod q`, with `m` in `a5`, `q` in `a6` and `t` a temporary:
`t = ⌊d · m / 2⁶⁴⌋`, then `d - t + 2¹³ t - 2²³ t - q`, fixed up. -/
def reduce (d t : Reg) : List Instr :=
  [.mulhu t d .a5, .sub d d t, .shift .sll .d t t 13, .add d d t, .shift .sll .d t t 10, .sub d d t,
    .sub d d .a6] ++ fixup d t .a6

/-- Entry `k` of the table `T`, through `t2`, at `[b + 4k]`. -/
def tabStep (T : Nat → Nat) (b : Reg) (k : Nat) : List Instr :=
  loadImm .t2 (T k) ++ [.store .w .t2 b (4 * k)]

/-- The 256 entries of `T` as `u32`s at `[b]`, through `t2`. -/
def table (T : Nat → Nat) (b : Reg) : List Instr := (List.range 256).flatMap (tabStep T b)

/-! ## `ntt` -/

/-- The butterfly on `[a2]` and `[a3]` with the zeta `a4`: `t = ζ·f[j + len]`
in `t0`, then `f[j + len] = f[j] - t` and `f[j] = f[j] + t`. -/
def bflyBody : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a3 0, .mul .t0 .a4 .t0] ++ reduce .t0 .t3 ++
  [.sub .t3 .t2 .t0] ++ fixup .t3 .t4 .a6 ++ [.store .w .t3 .a3 0, .add .t2 .t2 .t0,
    .sub .t2 .t2 .a6] ++ fixup .t2 .t4 .a6 ++
  [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)]

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2])
    (.seq (.loop (.block bflyBody) (.nonzero .t1))
      (.block [.addi .a2 .a3 0, .sub .t0 .a2 .a0]))

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)])
    (.seq (.loop nttBlockCode (.nonzero .t0))
      (.block [.shift .srl .d .a7 .a7 1, .addi .t0 .a7 (-2)]))

def ntt : Prog isa :=
  .seq (.block (table zetaTab .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 4, .li .a7 512] : List Instr)))
    (.loop nttLayerCode (.nonzero .t0))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[a2]` and `[a3]` with the zeta `a4`:
`f[j] = f[j] + f[j + len]`, then `f[j + len] = z·(f[j] - f[j + len])`. -/
def ibflyBody : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a3 0, .add .t3 .t2 .t0, .sub .t3 .t3 .a6] ++
  fixup .t3 .t4 .a6 ++ [.store .w .t3 .a2 0, .sub .t0 .t2 .t0] ++ fixup .t0 .t4 .a6 ++
  [.mul .t0 .a4 .t0] ++ reduce .t0 .t3 ++
  [.store .w .t0 .a3 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)]

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 (-4), .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2])
    (.seq (.loop (.block ibflyBody) (.nonzero .t1))
      (.block [.addi .a2 .a3 0, .sub .t0 .a2 .a0]))

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)])
    (.seq (.loop nttInvBlockCode (.nonzero .t0))
      (.block [.shift .sll .d .a7 .a7 1, .addi .t0 .a7 (-1024)]))

/-- `[a2] ← [a2] · a4 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.load .w .t2 .a2 0, .mul .t2 .t2 .a4] ++ reduce .t2 .t3 ++
  [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)]

def nttInv : Prog isa :=
  .seq (.block (table negZetaTab .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 1020, .li .a7 4] : List Instr)))
    (.seq (.loop nttInvLayerCode (.nonzero .t0))
    (.seq (.block (loadImm .a4 8347681 ++ ([.addi .a2 .a0 (-1024), .li .t1 256] : List Instr)))
      (.loop (.block scaleBody) (.nonzero .t1))))

/-! ## `multiplyNTT` and `multiplyAddNTT` -/

/-- `t0 = f[i] · g[i]`, then `t2 = h[i]` added for `multiplyAddNTT`. -/
def mulHead : List Instr := [.load .w .t0 .a1 0, .load .w .t2 .a2 0, .mul .t0 .t0 .t2]

/-- The reduced value stored to `h[i]`, and on to the next coefficient. -/
def mulTail : List Instr :=
  reduce .t0 .t2 ++ [.store .w .t0 .a0 0, .addi .a0 .a0 4, .addi .a1 .a1 4, .addi .a2 .a2 4, .addi .t1 .t1 (-1)]

def mulBody : List Instr := mulHead ++ mulTail

def mulAddBody : List Instr := mulHead ++ ([.load .w .t2 .a0 0, .add .t0 .t0 .t2] : List Instr) ++ mulTail

def mul : Prog isa := .seq (.block (consts ++ ([.li .t1 256] : List Instr))) (.loop (.block mulBody) (.nonzero .t1))

def mulAdd : Prog isa :=
  .seq (.block (consts ++ ([.li .t1 256] : List Instr))) (.loop (.block mulAddBody) (.nonzero .t1))

/-! ## `add` and `sub` -/

/-- The counter, and `q` in `a5`. -/
def polyInit : List Instr := .li .a2 256 :: loadImm .a5 8380417

def add : Prog isa := .seq (.block polyInit) (.loop (.block addBody) (.nonzero .a2))

def sub : Prog isa := .seq (.block polyInit) (.loop (.block subBody) (.nonzero .a2))

end VG.Impl.MlDsa.RISCV64.Arith
