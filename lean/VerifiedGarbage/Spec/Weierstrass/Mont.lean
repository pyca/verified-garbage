import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Spec.P192
import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Spec.Secp256k1

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, a step at a time

**Trusted** (as every file in `Spec/`). The contracts of three functions for
each modulus `m` of `moduli` (the primes `p` and the orders `n` of P-192,
P-224, P-256, P-384, P-521 and secp256k1), so that the code of a curve's functions can call one
copy of its field arithmetic instead of repeating it at every use:

* `vg_<curve>_mul_mod_<p|n>`: Montgomery's product, the number below `m`
  congruent to `a b R⁻¹` modulo `m`, with `R = 2^(64 k)` for numbers of `k`
  64-bit words, for `b` below `m` (and any `a`);
* `vg_<curve>_add_mod_<p|n>`: `(a + b) mod m`, for `a + b` below `2 m`;
* `vg_<curve>_sub_mod_<p|n>`: `(a - b) mod m`, for `a` and `b` below `m`.

They are not algorithms of a standard but the arithmetic every algorithm on
the curve is built from: what they compute is stated on integers, and an
implementation is free to call them in any form (Montgomery's or not) as long
as its own proof follows what they are.

The numbers live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of the curve's functions), each `k` 64-bit words, little-endian,
at a byte offset: `o` for the result, `a` and `b` for the operands
(`numAt`). The offsets are arguments, so that the result may be either
operand (`o = a` or `o = b`) and the caller keeps its numbers where it
likes. The `64 k` bytes below byte 4096 of `ws` (`ownAt`) are the function's
own working space, and the numbers lie below them (`Fits`), so that an
implementation reaches all of them with short offsets from the start of
`ws`. On return the function's own bytes are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value but the
result's (`Keeps`).

The result is below `m`. The operands' bounds are those an implementation
by Montgomery's multiplication and a conditional subtraction needs, which
let a caller convert a number below `R` to Montgomery's form (by `R² mod m`)
or reduce one below `2 m` (by adding zero). Everything is secret but the
pointer and the offsets, which are public, and the functions are constant
time.
-/

namespace VG.Spec.Weierstrass.Mont

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of the working space that a function uses for itself, for
numbers of `k` 64-bit words. -/
def ownBytes (k : Nat) : Nat := 64 * k

/-- Where they start: they end at byte 4096. -/
def ownAt (k : Nat) : Nat := 4096 - ownBytes k

/-- The number of `k` 64-bit words, little-endian, at byte offset `o` of the
working space `ws`. -/
def numAt (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) (8 * k)).toNat

/-- The number at offset `o` lies below the function's own working space. -/
abbrev Fits (k : Nat) (o : BitVec 32) : Prop := o.toNat + 8 * k ≤ ownAt k

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (k : Nat) (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt k ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + 8 * k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- A modulus: its curve's name (the functions are `vg_<curve>_*`, in the
Rust module `<curve>_mont`), which of the curve's numbers it is (`p` or
`n`), its value `m`, odd, and the count `k` of 64-bit words of the numbers,
with `m < 2^(64 k)`. -/
structure Modulus where
  curve : String
  which : String
  m : Nat
  k : Nat
  /-- How the documentation names the modulus. -/
  desc : String

namespace Modulus

variable (M : Modulus)

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * M.k)

/-- What each function requires of the offsets: the numbers lie below its
own working space. -/
def Fit (o a b : BitVec 32) : Prop := Fits M.k o ∧ Fits M.k a ∧ Fits M.k b

/-- `mul`: for `b` below `m`, the number at `o` is below `m` and congruent to
`a b R⁻¹`, that is, its product with `R` is congruent to `a b`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws b M.k < M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k < M.m ∧
      numAt m' ws o M.k * M.R % M.m = numAt m ws a M.k * numAt m ws b M.k % M.m ∧
      Keeps M.k ws o m m')
    (stack := stack)

/-- `add`: for `a + b` below `2 m`, the number at `o` is `(a + b) mod m`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws a M.k + numAt m ws b M.k < 2 * M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k = (numAt m ws a M.k + numAt m ws b M.k) % M.m ∧ Keeps M.k ws o m m')
    (stack := stack)

/-- `sub`: for `a` and `b` below `m`, the number at `o` is `(a - b) mod m`,
that is, `(a + m - b) mod m`. -/
def subContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws a M.k < M.m ∧ numAt m ws b M.k < M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k = (numAt m ws a M.k + M.m - numAt m ws b M.k) % M.m ∧ Keeps M.k ws o m m')
    (stack := stack)

/-- The Rust module of the curve's functions. -/
def module : String := M.curve ++ "_mont"

/-- The name of the function `op` modulo `m`. -/
def fn (op : String) : String := s!"vg_{M.curve}_{op}_mod_{M.which}"

/-- What the documentation says of every function. -/
def common : String :=
  s!"The numbers are {M.k} 64-bit words (`{8 * M.k}` bytes), little-endian, at the byte \
    offsets `o`, `a` and `b` of the working space `ws`; `o` may be `a` or `b`. Every byte of \
    `ws` but the result's and the function's own working space (bytes {ownAt M.k} to 4095) keeps \
    its value.\n\n\
    Contract: `mulContract`, `addContract` or `subContract` of \
    `VG.Spec.Weierstrass.Mont.Modulus`. Constant time: only the pointer and the offsets may \
    affect timing."

/-- The `# Safety` items but for what the signature gives, after `bound`,
what the function requires of its operands. -/
def safety (bound : String) : List String :=
  [s!"`o`, `a` and `b` plus {8 * M.k} must be at most {ownAt M.k}: bytes {ownAt M.k} to 4095 \
      of `ws` are the function's own working space.",
    bound,
    s!"Bytes {ownAt M.k} to 4095 of `ws` are unspecified on return and may hold intermediate \
      values, which the caller must destroy if they are secret."]

/-- `vg_<curve>_mul_mod_<which>` on every target. -/
def mulApi : Api where
  module := M.module
  name := M.fn "mul"
  sig := sig
  contracts := some fun A stack => M.mulContract A stack
  summary := s!"Montgomery's product modulo {M.desc}: writes the number below the modulus \
    congruent to `a b 2^-{64 * M.k}` to `o`. " ++ M.common
  safety := M.safety s!"The number at `b` must be below {M.desc}."

/-- `vg_<curve>_add_mod_<which>` on every target. -/
def addApi : Api where
  module := M.module
  name := M.fn "add"
  sig := sig
  contracts := some fun A stack => M.addContract A stack
  summary := s!"The sum modulo {M.desc}: writes `(a + b) mod` the modulus to `o`. " ++ M.common
  safety := M.safety s!"The sum of the numbers at `a` and `b` must be below twice {M.desc}."

/-- `vg_<curve>_sub_mod_<which>` on every target. -/
def subApi : Api where
  module := M.module
  name := M.fn "sub"
  sig := sig
  contracts := some fun A stack => M.subContract A stack
  summary := s!"The difference modulo {M.desc}: writes `(a - b) mod` the modulus to `o`. " ++
    M.common
  safety := M.safety s!"The numbers at `a` and `b` must be below {M.desc}."

end Modulus

/-! ## The moduli -/

def p192p : Modulus := ⟨"p192", "p", Spec.P192.p, 3, "P-192's prime `p`"⟩
def p192n : Modulus := ⟨"p192", "n", Spec.P192.n, 3, "P-192's order `n`"⟩
def p224p : Modulus := ⟨"p224", "p", Spec.P224.p, 4, "P-224's prime `p`"⟩
def p224n : Modulus := ⟨"p224", "n", Spec.P224.n, 4, "P-224's order `n`"⟩
def p256p : Modulus := ⟨"p256", "p", Spec.P256.p, 4, "P-256's prime `p`"⟩
def p256n : Modulus := ⟨"p256", "n", Spec.P256.n, 4, "P-256's order `n`"⟩
def p384p : Modulus := ⟨"p384", "p", Spec.P384.p, 6, "P-384's prime `p`"⟩
def p384n : Modulus := ⟨"p384", "n", Spec.P384.n, 6, "P-384's order `n`"⟩
def p521p : Modulus := ⟨"p521", "p", Spec.P521.p, 9, "P-521's prime `p`"⟩
def p521n : Modulus := ⟨"p521", "n", Spec.P521.n, 9, "P-521's order `n`"⟩
def secp256k1p : Modulus := ⟨"secp256k1", "p", Spec.Secp256k1.p, 4, "secp256k1's prime `p`"⟩
def secp256k1n : Modulus := ⟨"secp256k1", "n", Spec.Secp256k1.n, 4, "secp256k1's order `n`"⟩

/-- Every modulus. -/
def moduli : List Modulus :=
  [p192p, p192n, p224p, p224n, p256p, p256n, p384p, p384n, p521p, p521n, secp256k1p, secp256k1n]

end VG.Spec.Weierstrass.Mont
