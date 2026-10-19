module

public import VerifiedGarbage.TCB.Artifact

/-!
# Montgomery multiplication in a working space of fixed layout

**Trusted** (as every file in `Spec/`). A callable piece of the RSA
functions: `vg_rsa_mont_mul_{tag}_{n}` writes, at a byte offset `o` of a
working space, the Montgomery product of the numbers at offsets `a` and `b`,
modulo the number at a fixed offset. The RSA functions multiply at many
places of their code, at every width they support; with the modulus, its
inverse and the function's own working memory at fixed offsets of a layout,
and the operands given at run time, they share one copy of the code per
width and layout instead of repeating it at every use. It is not an
algorithm of a standard but the arithmetic the RSA functions are built from:
what it computes is stated on integers.

A `Layout` gives the width and the offsets, which the implementation chooses
for its working space: the modulus is a number of `8 n` bytes, little-endian,
at `modulus`, and `-m⁻¹ mod 2³²` a 32-bit word at `inv`. The operands and the
result are numbers of `8 n` bytes at the byte offsets `a`, `b` and `o`, which
are arguments; the result may be either operand, and the operands may be the
same number (a square). The function may change the bytes of its `scratch`
ranges and the result's; every other byte of the working space keeps its
value. Its timing may depend on the working space's address and on `o`, `a`
and `b`, not on the numbers.
-/

@[expose] public section

namespace VG.Spec.Rsa.MontMulAt

/-- The width and the fixed byte offsets of a multiplication's working space. -/
structure Layout where
  /-- Names the layout in the function's name. -/
  tag : String
  /-- The 64-bit words of the modulus, the operands and the result. -/
  n : Nat
  /-- The byte offset of the modulus. -/
  modulus : Nat
  /-- The byte offset of the 32-bit word `-m⁻¹ mod 2³²`. -/
  inv : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function may
  change, besides the result's. -/
  scratch : List (Nat × Nat)
  /-- The 64-bit words of the working space. -/
  words : Nat

/-- The number of `bytes` bytes, little-endian, at byte `off` of `ws`. -/
def numAt (m : Mem) (ws : Addr) (off bytes : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 off) bytes).toNat

/-- The `k` bytes at `x` lie before or after the range `r`. -/
def Apart (x k : Nat) (r : Nat × Nat) : Prop := x + k ≤ r.1 ∨ r.1 + r.2 ≤ x

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; L.words], o: u32, a: u32, b: u32`, the offsets public. -/
def sig (L : Layout) : Sig where
  params := [("ws", .array true .u64 L.words), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- For the numbers at `o`, `a` and `b` within the working space and apart
from the function's scratch, the result apart from the modulus and its
inverse, `-m⁻¹ mod 2³²` at `L.inv` (so the modulus `m` is odd), and the
number at `b` below `m`: the number at `o` is below `m` and its product with
`R = 2^(64 n)` is congruent to the product of the numbers at `a` and `b`
modulo `m`. Only the bytes of `L.scratch` and of the result may change. The
address of the working space and the offsets are public; the numbers, the
modulus among them, are secret. -/
def mulContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  (sig L).contract A
    (pre := fun ws o a b m =>
      let nb := 8 * L.n
      let M := numAt m ws L.modulus nb
      o.toNat + nb ≤ 8 * L.words ∧ a.toNat + nb ≤ 8 * L.words ∧ b.toNat + nb ≤ 8 * L.words ∧
        (∀ r ∈ L.scratch, Apart o.toNat nb r ∧ Apart a.toNat nb r ∧ Apart b.toNat nb r) ∧
        Apart o.toNat nb (L.modulus, nb) ∧ Apart o.toNat nb (L.inv, 4) ∧
        (M * numAt m ws L.inv 4 + 1) % 2 ^ 32 = 0 ∧ numAt m ws b.toNat nb < M)
    (post := fun ws o a b m m' _ =>
      let nb := 8 * L.n
      let M := numAt m ws L.modulus nb
      numAt m' ws o.toNat nb < M ∧
        numAt m' ws o.toNat nb * 2 ^ (64 * L.n) % M =
          numAt m ws a.toNat nb * numAt m ws b.toNat nb % M ∧
        Keeps ws L.words (L.scratch ++ [(o.toNat, nb)]) m m')
    (stack := stack)

/-- The ranges as the documentation lists them. -/
def rangesDoc (rs : List (Nat × Nat)) : String :=
  ", ".intercalate (rs.map fun (o, k) => s!"{o}..{o + k}")

/-- The multiplication of layout `L`, with the same meaning on every target
that registers it. -/
def mulApi (L : Layout) : Api where
  module := "rsa_mont"
  name := s!"vg_rsa_mont_mul_{L.tag}_{L.n}"
  sig := sig L
  contracts := some fun A stack => mulContract L A stack
  summary := s!"Montgomery multiplication at fixed offsets of a working space: writes at byte \
    `o` of `ws` the number below the modulus `m` congruent to `a b 2^(-{64 * L.n})` modulo \
    `m`, for the numbers `a` and `b` at bytes `a` and `b`, each of {8 * L.n} bytes, \
    little-endian, for the modulus `m` of {8 * L.n} bytes at byte {L.modulus} and \
    `-m⁻¹ mod 2^32` in the 32-bit word at byte {L.inv}. `o` may be `a` or `b`, and `a` may \
    be `b`. Every byte of `ws` but those of the ranges {rangesDoc L.scratch} (the \
    function's own) and of the result keeps its value.\n\n\
    Contract: `VG.Spec.Rsa.MontMulAt.mulContract`. Constant time but for the address of \
    `ws` and the offsets: timing does not depend on the numbers."
  safety := [s!"The {8 * L.n} bytes at each of `o`, `a` and `b` must lie within `ws`, apart \
      from the ranges {rangesDoc L.scratch}; those at `o` must also be apart from the \
      modulus (bytes {L.modulus}..{L.modulus + 8 * L.n}) and from bytes {L.inv}..{L.inv + 4}.",
    s!"The 32-bit word at byte {L.inv} of `ws` must be `-m⁻¹ mod 2^32` for the modulus `m` at \
      byte {L.modulus}, which must be odd.",
    "The number at `b` must be below `m`.",
    s!"The bytes {rangesDoc L.scratch} of `ws` are unspecified on return and may hold \
      intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.Rsa.MontMulAt
