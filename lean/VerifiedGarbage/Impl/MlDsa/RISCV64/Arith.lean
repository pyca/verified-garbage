module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: the arithmetic of polynomials

As ML-KEM's on RISC-V (`Impl/MlKem/RISCV64/Ntt.lean`), for
`q = 8380417 = 2²³ − 2¹³ + 1`: the coefficients are `u32`s, loaded
zero-extended (`lwu`) and stored as the low word (`sw`), and the arithmetic
is on all 64 bits.

A product of two words (or that plus a reduced value) `x` is reduced by
Barrett's method with `mulhu`: `t = ⌊x · m / 2⁶⁴⌋` for `m = ⌊2⁶⁴ / q⌋` is
`⌊x / q⌋` or one less, so `x - t·q` (`barrett`, the product `t·q` by `mul`)
is less than `2q` and congruent to `x`; a subtraction of `q` and a `fixup`
(`Impl/MlKem/RISCV64/Poly.lean`) finish it (`reduce`).

The butterflies are lazy, as x86-64's (`Impl/MlDsa/X86_64/Arith/Lazy.lean`):
each reduces only its product, to `barrett`'s value in `[0, 2q)`, and stores
the sum and the difference as they are, the difference plus `2q` (in `t5`)
so that it is not negative; each of the eight layers of `ntt` thus adds less
than `2q` to the coefficients, which stay less than `17 q`, and a last loop
reduces them (`canonBody`). Those of `nttInv` add the two coefficients and
reduce the product of the zeta and their difference plus `128 q` (in `t5`),
so each layer at most doubles the bound, which stays less than `256 q < 2³¹`;
the multiplication by `256⁻¹` reduces them.
`a5 = m` and `a6 = q` throughout (`consts`).

The tables of the 256 zetas `ζ^BitRev8(m) mod q` (`zetaTab`) and of their
negations (`negZetaTab`, the `z` of Algorithm 42) are stored in `scratch`,
as 256 `u32`s (`table`: each entry a `lui` and an `addi`, then a store,
through `t2`), and read in order through a pointer. The functions use only
registers the calling convention lets them clobber, make no calls and use
no stack.

* `vg_mldsa_ntt(f = a0, scratch = a1)`: the eight layers of Algorithm 41,
  each its own code (`nttLayerCode o`, `len` from 128, halved, down to 1),
  so that `o = 4 len` is an offset in the instructions: with `a0 = f + 1024`
  and the zetas read from `m = 1` up, a block loads its zeta and sets `a3`
  to the end of its first half; each butterfly is on `a2` and `o(a2)`, until
  `a2 = a3`; the next block starts `o` bytes on, until `a2 = a0`. Then every
  coefficient reduced.
* `vg_mldsa_inv_ntt(f = a0, scratch = a1)`: the same for the eight layers of
  Algorithm 42, `len` from 1, doubled, up to 128, the negated zetas read
  from `m = 255` down, and the inverse butterflies; then every coefficient
  times `8347681 = 256⁻¹ mod q`.
* `vg_mldsa_multiply_ntt(h = a0, f = a1, g = a2)`: `h[i] = f[i] · g[i]`,
  reduced, counted by `t1`; `vg_mldsa_multiply_add_ntt` adds `h[i]` to the
  product before reducing it.
* `vg_mldsa_add(f = a0, g = a1)`, `vg_mldsa_sub(f = a0, g = a1)`: ML-KEM's
  loops (`Impl.MlKem.RISCV64.addBody`, `subBody`) with `q` in `a5`.

Every address is a pointer plus a constant, and every branch depends on a
counter or compares two pointers: only the pointers can affect timing.
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

/-- `d - ⌊d · m / 2⁶⁴⌋ · q`, in `[0, 2q)`, with `m` in `a5`, `q` in `a6` and
`t` a temporary. -/
def barrett (d t : Reg) : List Instr := [.mulhu t d .a5, .mul t t .a6, .sub d d t]

/-- `d ← d mod q`: `barrett`, then `- q`, fixed up. -/
def reduce (d t : Reg) : List Instr := barrett d t ++ [.sub d d .a6] ++ fixup d t .a6

/-- Entry `k` of the table `T`, through `t2`, at `[b + 4k]`. -/
def tabStep (T : Nat → Nat) (b : Reg) (k : Nat) : List Instr :=
  loadImm .t2 (T k) ++ [.store .w .t2 b (4 * k)]

/-- The 256 entries of `T` as `u32`s at `[b]`, through `t2`. -/
def table (T : Nat → Nat) (b : Reg) : List Instr := (List.range 256).flatMap (tabStep T b)

/-! ## `ntt` -/

/-- The lazy butterfly on `[a2]` and `[a3]` with the zeta `a4`: `t = ζ·f[j + len]`
less a multiple of `q`, in `[0, 2q)` (`barrett`), in `t0`, then
`f[j + len] = f[j] - t + 2q` (`2q` in `t5`) and `f[j] = f[j] + t`. -/
def bflyBody (o : Nat) : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a2 o, .mul .t0 .a4 .t0] ++ barrett .t0 .t3 ++
  [.sub .t3 .t2 .t0, .add .t3 .t3 .t5, .store .w .t3 .a2 o, .add .t2 .t2 .t0,
    .store .w .t2 .a2 0, .addi .a2 .a2 4]

/-- A block, with `o = 4 len`: its zeta, the end of its first half in `a3`,
then `len` butterflies, and the next block. -/
def nttBlockCode (o : Nat) : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .addi .a3 .a2 o])
    (.seq (.loop (.block (bflyBody o)) (.ne .a2 .a3)) (.block [.addi .a2 .a2 o]))

/-- A layer, with `o = 4 len`: its blocks. -/
def nttLayerCode (o : Nat) : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)]) (.loop (nttBlockCode o) (.ne .a2 .a0))

/-- The offsets `4 len` of the layers of `ntt`, and of `nttInv` reversed. -/
def nttOffs : List Nat := [512, 256, 128, 64, 32, 16, 8, 4]

/-- Layers, one after the other. -/
def layers (code : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | o :: os => .seq (code o) (layers code os)

/-- `[a2] ← [a2] mod q`, and on to the next coefficient. -/
def canonBody : List Instr :=
  [.load .w .t2 .a2 0] ++ reduce .t2 .t3 ++ [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)]

def ntt : Prog isa :=
  .seq (.block (table zetaTab .a1 ++ consts ++
      ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4] : List Instr)))
    (.seq (layers nttLayerCode nttOffs)
      (.seq (.block [.addi .a2 .a0 (-1024), .li .t1 256]) (.loop (.block canonBody) (.nonzero .t1))))

/-! ## `nttInv` -/

/-- The lazy inverse butterfly on `[a2]` and `[a3]` with the zeta `a4`:
`f[j] = f[j] + f[j + len]`, then `f[j + len] = z·(f[j] - f[j + len] + 128 q)`
less a multiple of `q`, in `[0, 2q)` (`barrett`; `128 q` in `t5`). -/
def ibflyBody (o : Nat) : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a2 o, .add .t3 .t2 .t0, .store .w .t3 .a2 0, .sub .t0 .t2 .t0,
    .add .t0 .t0 .t5, .mul .t0 .a4 .t0] ++ barrett .t0 .t3 ++
  [.store .w .t0 .a2 o, .addi .a2 .a2 4]

/-- A block, with `o = 4 len`: its zeta, the end of its first half in `a3`,
then `len` inverse butterflies, and the next block. -/
def nttInvBlockCode (o : Nat) : Prog isa :=
  .seq (.block [.load .w .a4 .a1 0, .addi .a1 .a1 (-4), .addi .a3 .a2 o])
    (.seq (.loop (.block (ibflyBody o)) (.ne .a2 .a3)) (.block [.addi .a2 .a2 o]))

/-- A layer, with `o = 4 len`: its blocks. -/
def nttInvLayerCode (o : Nat) : Prog isa :=
  .seq (.block [.addi .a2 .a0 (-1024)]) (.loop (nttInvBlockCode o) (.ne .a2 .a0))

/-- `[a2] ← [a2] · a4 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.load .w .t2 .a2 0, .mul .t2 .t2 .a4] ++ reduce .t2 .t3 ++
  [.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)]

def nttInv : Prog isa :=
  .seq (.block (table negZetaTab .a1 ++ consts ++ loadImm .t5 1072693376 ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 1020] : List Instr)))
    (.seq (layers nttInvLayerCode nttOffs.reverse)
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
