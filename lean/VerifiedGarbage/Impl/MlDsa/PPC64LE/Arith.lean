module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on PPC64LE: the arithmetic of polynomials

As ML-KEM's on PPC64LE (`Impl/MlKem/PPC64LE/Ntt.lean`), for
`q = 8380417 < 2²³`: the coefficients are `u32`s, loaded zero-extended
(`lwz`) and stored as the low word (`stw`), and the arithmetic is on all 64
bits. A product of two reduced values has up to 46 bits, and is reduced by
`reduce`: the Barrett reduction `VG.Proof.MlDsa.Arith.barrett` of any 64-bit
`x`, `x - ⌊x · ⌊2⁶⁴ / q⌋ / 2⁶⁴⌋ · q` (the high half of the product by
`mulhdu`), which leaves a value less than `2q` congruent to `x`, then a
subtraction of `q` and a `fixup` (`Impl/MlKem/PPC64LE/Poly.lean`).
`r8 = ⌊2⁶⁴ / q⌋` and `r9 = q` throughout (`consts`). `mulld` and `mulhdu`
are the model's only multiplications, and their timing does not depend on
their operands (see `TCB/PPC64LE/Isa.lean`).

* `vg_mldsa_ntt(f = r3, scratch = r4)`: the eight layers of Algorithm 41 as
  ML-KEM's seven, with the table of the 256 zetas `ζ^BitRev8(m) mod q`
  (`zetaTab`) stored in `scratch` (`table`, through `r12`) and read from
  `m = 1` up.
* `vg_mldsa_inv_ntt(f = r3, scratch = r4)`: the eight layers of Algorithm
  42, with the table of the negated zetas `-ζ^BitRev8(m) mod q`
  (`negZetaTab`, the `z` of Algorithm 42) read from `m = 255` down, and the
  inverse butterflies; then every coefficient times `8347681 = 256⁻¹ mod q`.

The scratch space holds the table, and nothing more: the butterflies' `r14`
and `r15` are saved in a frame each on the stack (`saving`), 96 bytes.

* `vg_mldsa_multiply_ntt(h = r3, f = r4, g = r5)`: `h[i] = f[i] · g[i]`,
  reduced, counted by `r6`; `vg_mldsa_multiply_add_ntt` adds `h[i]` to the
  product before reducing it.
* `vg_mldsa_add(f = r3, g = r4)`, `vg_mldsa_sub(f = r3, g = r4)`: ML-KEM's
  loops (`Impl.MlKem.PPC64LE.addBody`, `subBody`) with `q = 8380417` in `r8`.

Every address is a pointer plus a constant, and every branch depends on a
counter or a pointer: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Arith

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (fixup addBody subBody)

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- `r ← v` for `v < 2³¹`: its high and low halves, by `lis` and `ori`. -/
def loadImm (r : Reg) (v : Nat) : List Instr :=
  [.lis r (BitVec.ofNat 16 (v / 65536)), .ori r r (BitVec.ofNat 16 (v % 65536))]

/-- `r ← q = 0x7FE001`. -/
def loadQ (r : Reg) : List Instr := loadImm r 8380417

/-- `r8 = ⌊2⁶⁴ / q⌋ = 0x200801C0601`, `r9 = q`. -/
def consts : List Instr :=
  [.lis .r8 0x200, .ori .r8 .r8 0x801C, .lsl .r8 .r8 16, .ori .r8 .r8 0x0601] ++ loadQ .r9

/-- `d ← d mod q`, for any `d`, with `⌊2⁶⁴ / q⌋` in `r8`, `q` in `r9` and
`t` a temporary. -/
def reduce (d t : Reg) : List Instr :=
  [.mulhu t d .r8, .mul t t .r9, .sub d d t, .sub d d .r9] ++ fixup d t .r9

/-- Entry `k` of the table `T`, through `r12`, at `[b + 4k]`. -/
def tabStep (T : Nat → Nat) (b : Reg) (k : Nat) : List Instr :=
  loadImm .r12 (T k) ++ [.store .w .r12 b (4 * k)]

/-- The 256 entries of `T` as `u32`s at `[b]`, through `r12`. -/
def table (T : Nat → Nat) (b : Reg) : List Instr := (List.range 256).flatMap (tabStep T b)

/-- `body`, with `r14` and `r15` saved in a frame each around it. -/
def saving (body : Prog isa) : Prog isa :=
  .frame (.push .r14) (.frame (.push .r15) body (.pop .r15)) (.pop .r14)

/-! ## `ntt` -/

/-- The butterfly on `[r5]` and `[r6]` with the zeta `r7`: `t = ζ·f[j + len]`
in `r0`, then `f[j + len] = f[j] - t` and `f[j] = f[j] + t`. -/
def bflyBody : List Instr :=
  [.load .w .r12 .r5 0, .load .w .r0 .r6 0, .mul .r0 .r7 .r0] ++ reduce .r0 .r14 ++
  [.sub .r14 .r12 .r0] ++ fixup .r14 .r15 .r9 ++ [.store .w .r14 .r6 0, .add .r12 .r12 .r0,
    .sub .r12 .r12 .r9] ++ fixup .r12 .r15 .r9 ++
  [.store .w .r12 .r5 0, .addi .r5 .r5 4, .addi .r6 .r6 4, .subi .r11 .r11 1]

/-- A block: its zeta, then `len` butterflies. -/
def nttBlockCode : Prog isa :=
  .seq (.block [.load .w .r7 .r4 0, .addi .r4 .r4 4, .add .r6 .r5 .r10, .lsr .d .r11 .r10 2])
    (.seq (.loop (.block bflyBody) (.nonzero .d .r11))
      (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]))

/-- A layer: its blocks. -/
def nttLayerCode : Prog isa :=
  .seq (.block [.subi .r5 .r3 1024])
    (.seq (.loop nttBlockCode (.nonzero .d .r0)) (.block [.lsr .d .r10 .r10 1, .subi .r0 .r10 2]))

def ntt : Prog isa :=
  saving (.seq (.block (table zetaTab .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr)))
    (.loop nttLayerCode (.nonzero .d .r0)))

/-! ## `nttInv` -/

/-- The inverse butterfly on `[r5]` and `[r6]` with the zeta `r7`:
`f[j] = f[j] + f[j + len]`, then `f[j + len] = z·(f[j] - f[j + len])`. -/
def ibflyBody : List Instr :=
  [.load .w .r12 .r5 0, .load .w .r0 .r6 0, .add .r14 .r12 .r0, .sub .r14 .r14 .r9] ++
  fixup .r14 .r15 .r9 ++ [.store .w .r14 .r5 0, .sub .r0 .r12 .r0] ++ fixup .r0 .r15 .r9 ++
  [.mul .r0 .r7 .r0] ++ reduce .r0 .r14 ++
  [.store .w .r0 .r6 0, .addi .r5 .r5 4, .addi .r6 .r6 4, .subi .r11 .r11 1]

/-- A block: its zeta, then `len` inverse butterflies. -/
def nttInvBlockCode : Prog isa :=
  .seq (.block [.load .w .r7 .r4 0, .subi .r4 .r4 4, .add .r6 .r5 .r10, .lsr .d .r11 .r10 2])
    (.seq (.loop (.block ibflyBody) (.nonzero .d .r11))
      (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]))

/-- A layer: its blocks. -/
def nttInvLayerCode : Prog isa :=
  .seq (.block [.subi .r5 .r3 1024])
    (.seq (.loop nttInvBlockCode (.nonzero .d .r0))
      (.block [.lsl .r10 .r10 1, .subi .r0 .r10 1024]))

/-- `[r5] ← [r5] · r7 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.load .w .r12 .r5 0, .mul .r12 .r12 .r7] ++ reduce .r12 .r14 ++
  [.store .w .r12 .r5 0, .addi .r5 .r5 4, .subi .r11 .r11 1]

def nttInv : Prog isa :=
  saving (.seq (.block (table negZetaTab .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 1020, .li .r10 4] : List Instr)))
    (.seq (.loop nttInvLayerCode (.nonzero .d .r0))
    (.seq (.block (loadImm .r7 8347681 ++ ([.subi .r5 .r3 1024, .li .r11 256] : List Instr)))
      (.loop (.block scaleBody) (.nonzero .d .r11)))))

/-! ## `multiplyNTT` and `multiplyAddNTT` -/

/-- `r7 = f[i] · g[i]`, then `r10 = h[i]` added for `multiplyAddNTT`. -/
def mulHead : List Instr := [.load .w .r7 .r4 0, .load .w .r10 .r5 0, .mul .r7 .r7 .r10]

/-- The reduced value stored to `h[i]`, and on to the next coefficient. -/
def mulTail : List Instr :=
  reduce .r7 .r10 ++ [.store .w .r7 .r3 0, .addi .r3 .r3 4, .addi .r4 .r4 4, .addi .r5 .r5 4, .subi .r6 .r6 1]

def mulBody : List Instr := mulHead ++ mulTail

def mulAddBody : List Instr := mulHead ++ ([.load .w .r10 .r3 0, .add .r7 .r7 .r10] : List Instr) ++ mulTail

def mul : Prog isa := .seq (.block (consts ++ ([.li .r6 256] : List Instr))) (.loop (.block mulBody) (.nonzero .d .r6))

def mulAdd : Prog isa :=
  .seq (.block (consts ++ ([.li .r6 256] : List Instr))) (.loop (.block mulAddBody) (.nonzero .d .r6))

/-! ## `add` and `sub` -/

def add : Prog isa := .seq (.block (.li .r5 256 :: loadQ .r8)) (.loop (.block addBody) (.nonzero .d .r5))

def sub : Prog isa := .seq (.block (.li .r5 256 :: loadQ .r8)) (.loop (.block subBody) (.nonzero .d .r5))

end VG.Impl.MlDsa.PPC64LE.Arith
