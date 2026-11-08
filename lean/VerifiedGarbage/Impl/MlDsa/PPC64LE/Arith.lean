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
`r8 = ⌊2⁶⁴ / q⌋` and `r9 = q` (`reduce`). `mulld` and `mulhdu`
are the model's only multiplications, and their timing does not depend on
their operands (see `TCB/PPC64LE/Isa.lean`).

`vg_mldsa_ntt`, `vg_mldsa_inv_ntt`, `vg_mldsa_multiply_ntt` and
`vg_mldsa_multiply_add_ntt` are vector code (`VNtt.lean`, `VNttInv.lean`,
`VMul.lean`); `saving` saves `r14` and `r15` for the callers' frames.

* `vg_mldsa_add(f = r3, g = r4)`, `vg_mldsa_sub(f = r3, g = r4)`: ML-KEM's
  loops (`Impl.MlKem.PPC64LE.addBody`, `subBody`) with `q = 8380417` in `r8`.

Every address is a pointer plus a constant, and every branch depends on a
counter or a pointer: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Arith

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (fixup addBody subBody)

/-- `r ← v` for `v < 2³¹`: its high and low halves, by `lis` and `ori`. -/
def loadImm (r : Reg) (v : Nat) : List Instr :=
  [.lis r (BitVec.ofNat 16 (v / 65536)), .ori r r (BitVec.ofNat 16 (v % 65536))]

/-- `r ← q = 0x7FE001`. -/
def loadQ (r : Reg) : List Instr := loadImm r 8380417

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

/-! ## `add` and `sub` -/

def add : Prog isa := .seq (.block (.li .r5 256 :: loadQ .r8)) (.loop (.block addBody) (.nonzero .d .r5))

def sub : Prog isa := .seq (.block (.li .r5 256 :: loadQ .r8)) (.loop (.block subBody) (.nonzero .d .r5))

end VG.Impl.MlDsa.PPC64LE.Arith
