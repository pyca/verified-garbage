import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Spec.P384

/-!
# Inverses modulo a curve's prime and order, in its working space, as functions

**Trusted** (as every file in `Spec/`). The contracts of two functions for
each curve of `curves` (so far P-384), on the working space where the x86-64
code of the curve's ECDSA signature, verification and public key derivation
keeps its numbers, so that they can call one copy of each inversion instead
of repeating it:

* `vg_<curve>_inv_mod_p(ws)`: `A = Z^(p - 2)` modulo the curve's prime `p`,
  for the number `Z` at slot 16 (the code's `Z` coordinate of `[k]G`);
* `vg_<curve>_inv_mod_n(ws)`: `A = x^(n - 2)` modulo the curve's order `n`,
  for the number `x` at slot 37 (the code's scalar to invert).

Both numbers and the result `A` (slot 29) are in Montgomery's form modulo
their modulus `m` (`p` or `n`): `k` 64-bit words, little-endian, below `m`,
standing for `x R⁻¹` with `R = 2^(64 k)` and `R⁻¹ = R^(m-2)` (`dec`, as
`Spec/Weierstrass/Point.lean` decodes coordinates modulo `p`). The result is
stated as the power `pow (dec Z) (m - 2)` of `Weierstrass.pow`, which for a
prime `m` is the inverse of a nonzero `Z` (Fermat's little theorem) and zero
for zero; the code computes it as an inverse, by divsteps, which the proofs
show equal for the curve's prime `p` and order `n`.

The working space `ws` of 8192 bytes is the x86-64 code's: numbers of `k`
words in slots from byte 64 (`slot`), where the caller provides `p` (slot 0)
or `n` (slot 1) and the number to invert. The functions take no offsets.
Slot 30, the curve's temporary slot (`tmpAt`) and the `64 k + 64` bytes from
`workAt` (past the code's three tables of bits) are the functions' own working
space (`Own`); on return they are unspecified and may hold intermediate
values, secret ones among them, and the caller's callee-saved registers.
Every other byte of `ws` keeps its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

namespace VG.Spec.Weierstrass.Inverse

open Mont (wsBytes numAt)

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- A curve whose inversions are functions: the curve `W` (its prime `p` and
order `n`), its name (the functions are `vg_<curve>_inv_mod_p` and
`vg_<curve>_inv_mod_n`, in the Rust module `<curve>_inverse`), the count `k`
of 64-bit words of a number, with `p, n < 2^(64 k)`, how the documentation
names it, and the slot of its products' temporary area. -/
structure Curve where
  W : Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where `p` is. -/
def pAt : Nat := C.slot 0

/-- Where `n` is. -/
def nAt : Nat := C.slot 1

/-- Where `Z`, the number `inv_mod_p` inverts, is. -/
def zAt : Nat := C.slot 16

/-- Where `x`, the number `inv_mod_n` inverts, is. -/
def xAt : Nat := C.slot 37

/-- Where the result `A` is. -/
def outAt : Nat := C.slot 29

/-- Where the products' temporary area is. -/
def tmpAt : Nat := C.slot C.tmp

/-- Where the inversion's working area is: past three tables of `64 k + 8`
bytes from slot 45. -/
def workAt : Nat := C.slot 45 + 3 * (64 * C.k + 8)

/-- The bytes of the working area. -/
def workLen : Nat := 64 * C.k + 64

/-- Byte `i` is in the functions' own working space: slot 30, the temporary
slot, or the working area. -/
def Own (i : Nat) : Prop :=
  (C.slot 30 ≤ i ∧ i < C.slot 31) ∨ (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨
    (C.workAt ≤ i ∧ i < C.workAt + C.workLen)

/-- Every byte of `ws` but those of the own working space and of the result
keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → (i < C.outAt ∨ C.outAt + 8 * C.k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The number of `k` words at offset `o` of `ws`. -/
def num (ws : Addr) (m : Mem) (o : Nat) : Nat := numAt m ws (BitVec.ofNat 32 o) C.k

/-- The element of `ℤ/mℤ` that the number `x` stands for in Montgomery's
form: `x R⁻¹`, with `R = 2^(64 k)` and `R⁻¹ = R^(m-2)`. -/
def dec (mod : Nat) [NeZero mod] (x : Nat) : Fin mod :=
  Fin.ofNat mod x * Weierstrass.pow (Fin.ofNat mod (2 ^ (64 * C.k))) (mod - 2)

/-- The inversion modulo `mod`, at `modAt`, of the number at `inAt`: the
result below `mod`, standing for the power `(m - 2)` of what the number
stands for, and every other byte of `ws` but the own working space's kept. -/
def invContract {I : ISA} (A : Abi I) (mod : Nat) [NeZero mod] (modAt inAt : Nat)
    (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.num ws m modAt = mod ∧ C.num ws m inAt < mod)
    (post := fun ws m m' _ => C.num ws m' C.outAt < mod ∧
      C.dec mod (C.num ws m' C.outAt) = Weierstrass.pow (C.dec mod (C.num ws m inAt)) (mod - 2) ∧
      C.Keeps ws m m')
    (stack := stack)

/-- `inv_mod_p`: `A = Z^(p-2)` modulo `p`. -/
def invPContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  C.invContract A C.W.p C.pAt C.zAt stack

/-- `inv_mod_n`: `A = x^(n-2)` modulo `n`. -/
def invNContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  C.invContract A C.W.n C.nAt C.xAt stack

/-! ## The functions -/

/-- The Rust module of the curve's functions. -/
def module : String := C.curve ++ "_inverse"

/-- Where the documentation says a range of bytes is. -/
def rangeDoc (o n : Nat) : String := s!"{o} to {o + n - 1}"

/-- What the documentation says the functions' own working space is. -/
def ownDoc : String :=
  s!"Bytes {rangeDoc (C.slot 30) (8 * C.k)}, {rangeDoc C.tmpAt (8 * C.k)} and \
    {rangeDoc C.workAt C.workLen} of `ws`"

/-- What the documentation says of both functions. -/
def common (mod what : String) (modAt inAt : Nat) : String :=
  s!"Numbers are {C.k} 64-bit words (`{8 * C.k}` bytes), little-endian, in Montgomery's form \
    modulo {C.desc}'s {what} `{mod}`. The function reads `{mod}` at byte {modAt} and the number to \
    invert at byte {inAt}, and writes the result at bytes {rangeDoc C.outAt (8 * C.k)}, below \
    `{mod}`. {C.ownDoc} are the function's own working space; every other byte of `ws` but the \
    result's keeps its value. Constant time: only the pointer may affect timing."

/-- The `# Safety` items but for what the signature gives. -/
def safety (mod what : String) (modAt inAt : Nat) : List String :=
  [s!"The {C.k} words at byte {modAt} of `ws` must be {C.desc}'s {what} `{mod}`, and the number \
      at byte {inAt} must be below it.",
    s!"{C.ownDoc} are unspecified on return and may hold intermediate values, which are secret \
      and which the caller must destroy."]

/-- `vg_<curve>_inv_mod_p` on every target. -/
def invPApi : Api where
  module := C.module
  name := s!"vg_{C.curve}_inv_mod_p"
  sig := sig
  contracts := some fun A stack => C.invPContract A stack
  summary := s!"The power `A = Z^(p-2)` modulo {C.desc}'s prime `p` (the inverse of `Z` if it \
    is nonzero), of the number `Z` at byte {C.zAt} of `ws`. " ++
    C.common "p" "prime" C.pAt C.zAt ++ "\n\n\
    Contract: `invPContract` of `VG.Spec.Weierstrass.Inverse.Curve`."
  safety := C.safety "p" "prime" C.pAt C.zAt

/-- `vg_<curve>_inv_mod_n` on every target. -/
def invNApi : Api where
  module := C.module
  name := s!"vg_{C.curve}_inv_mod_n"
  sig := sig
  contracts := some fun A stack => C.invNContract A stack
  summary := s!"The power `A = x^(n-2)` modulo {C.desc}'s order `n` (the inverse of `x` if it \
    is nonzero), of the number `x` at byte {C.xAt} of `ws`. " ++
    C.common "n" "order" C.nAt C.xAt ++ "\n\n\
    Contract: `invNContract` of `VG.Spec.Weierstrass.Inverse.Curve`."
  safety := C.safety "n" "order" C.nAt C.xAt

end Curve

/-! ## The curves -/

def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384", tmp := 83 }

/-- Every curve. -/
def curves : List Curve := [p384]

end VG.Spec.Weierstrass.Inverse
