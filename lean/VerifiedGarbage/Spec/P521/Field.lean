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

/-- `vg_p521_mul_mont(out: *mut [u64; 9], a: *const [u64; 9], b: *const [u64; 9])`. -/
def mulMontSig : Sig where
  params := [("out", .array true .u64 9), ("a", .array false .u64 9), ("b", .array false .u64 9)]

/-- If `b < p`: writes to `out` the number below `p` congruent to
`a · b · R⁻¹` modulo `p`. -/
def mulMontContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulMontSig.contract A
    (pre := fun _out _a b m => feAt m b < p)
    (post := fun out a b m m' _ =>
      feAt m' out < p ∧ feAt m' out * montR % p = feAt m a * feAt m b % p)
    (stack := stack)

/-- `vg_p521_sqr_mont(out: *mut [u64; 9], a: *const [u64; 9])`. -/
def sqrMontSig : Sig where
  params := [("out", .array true .u64 9), ("a", .array false .u64 9)]

/-- If `a < p`: writes to `out` the number below `p` congruent to
`a · a · R⁻¹` modulo `p`. -/
def sqrMontContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sqrMontSig.contract A
    (pre := fun _out a m => feAt m a < p)
    (post := fun out a m m' _ =>
      feAt m' out < p ∧ feAt m' out * montR % p = feAt m a * feAt m a % p)
    (stack := stack)

/-- What the documentation says of a field element. -/
def feDoc : String :=
  "A field element is 9 64-bit words, least significant first."

/-- `vg_p521_mul_mont` on every target. -/
def mulMontApi : Api where
  module := "p521"
  name := "vg_p521_mul_mont"
  sig := mulMontSig
  contracts := some fun A stack => mulMontContract A stack
  summary := "Montgomery multiplication in P-521's field GF(p), `p = 2^521 - 1`: writes to \
    `*out` the field element below `p` congruent to `a · b · 2^-576` modulo `p`, for the field \
    elements `*a` and `*b`. " ++ feDoc ++ "\n\n\
    Contract: `VG.Spec.P521.mulMontContract`. Constant time: only the pointers may affect \
    timing."
  safety := ["`*b` must be below `p`."]

/-- `vg_p521_sqr_mont` on every target. -/
def sqrMontApi : Api where
  module := "p521"
  name := "vg_p521_sqr_mont"
  sig := sqrMontSig
  contracts := some fun A stack => sqrMontContract A stack
  summary := "Montgomery squaring in P-521's field GF(p), `p = 2^521 - 1`: writes to `*out` \
    the field element below `p` congruent to `a · a · 2^-576` modulo `p`, for the field element \
    `*a`. " ++ feDoc ++ "\n\n\
    Contract: `VG.Spec.P521.sqrMontContract`. Constant time: only the pointers may affect \
    timing."
  safety := ["`*a` must be below `p`."]

end VG.Spec.P521
