module

public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.TCB.Artifact

/-!
# P-521's field arithmetic: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of two functions of
the field `GF(p)` of P-521 (`p = 2⁵²¹ - 1`, `Spec/P521.lean`), so that the
implementations of the curve's operations can call one copy of their field
arithmetic rather than repeat it:

* `vg_p521_mul_mont`: Montgomery multiplication, `a · b · R⁻¹ mod p`;
* `vg_p521_sqr_mont`: Montgomery squaring, `a · a · R⁻¹ mod p`;

with `R = 2⁵⁷⁶` (`montR`), the radix to the power of the number of words,
`2^(64 · 9)`. `R` is invertible modulo `p` (`p` is odd), so the result is
the one number below `p` congruent to `a · b · R⁻¹`: the postconditions
state it as `out < p` and `out · R ≡ a · b (mod p)`.

A field element is 9 words of 64 bits, least significant first (`feAt`):
any number below `2⁵⁷⁶`, of which the functions take the second operand
below `p` and return their result below `p`. Everything but the pointers is
secret, and the functions are constant time.
-/

@[expose] public section

namespace VG.Spec.P521

/-- The Montgomery radix of P-521's field arithmetic, `2^(64 · 9)`. -/
def montR : Nat := 2 ^ 576

/-- The number the 9 words of 64 bits at `p` hold, least significant
first. -/
def feAt (m : Mem) (p : Addr) : Nat :=
  (List.range 9).foldr (fun i acc => (m.readW (p + BitVec.ofNat 64 (8 * i)) 64).toNat + 2 ^ 64 * acc) 0

end VG.Spec.P521
