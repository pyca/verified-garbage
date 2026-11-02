module

public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery multiplication at offsets given at run time

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable piece of the RSA
functions: `vg_rsa_mont_mul_at` writes, at a byte offset `o` of a working
space, the Montgomery product of the numbers at the offsets `a` and `b`,
modulo the number at the offset `m`, all of `8 n` bytes for the width `n`.
Unlike `vg_rsa_mont_mul` (`MontContract.lean`), whose numbers are arrays of 64-bit
words in the fixed layout of the RSA functions' working space, every offset
is an argument and the inverse is a 32-bit word, so that a 32-bit target's
RSA functions, at every width they support, call one copy of the code from
the layouts of their own. It is not an algorithm of a
standard but the arithmetic the RSA functions are built from: what it
computes is stated on integers.

The modulus, the operands and the result are numbers of `8 n` bytes,
little-endian; `-m⁻¹ mod 2³²` is the 32-bit word at the offset `inv`. The
function has the `scratchBytes n` bytes at the offset `s` for its own; it
may change them and the result's, and every other byte of the working space
keeps its value. The result may be either operand, and the operands may be
the same number (a square). Its timing may depend on the working space's
address and length, on the width and on the offsets, not on the numbers.
-/

@[expose] public section

namespace VG.Proof.Rsa.MontMul

/-- The bytes of the function's own range at width `n`: room for a product
of `2 n` words and its carry word, a number of `n` words, and 56 bytes. -/
def scratchBytes (n : Nat) : Nat := 24 * n + 56

/-- The number of `bytes` bytes, little-endian, at byte `off` of `ws`. -/
def numAt (m : Mem) (ws : Addr) (off bytes : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 off) bytes).toNat

/-- The `k` bytes at `x` lie before or after the range `r`. -/
def Apart (x k : Nat) (r : Nat × Nat) : Prop := x + k ≤ r.1 ∨ r.1 + r.2 ≤ x

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut u64, ws_len: usize`, then the width `n` and the byte offsets
`m`, `inv`, `s`, `o`, `a` and `b`, all public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("n", .int .u32 true), ("m", .int .u32 true),
    ("inv", .int .u32 true), ("s", .int .u32 true), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- For a positive width `n`, every range within the working space, the
function's own range (`s`, `scratchBytes n` bytes) apart from the modulus,
its inverse and the operands, the result apart from them too and from the
modulus and its inverse, `-m⁻¹ mod 2³²` at `inv` (so the modulus `M` is
odd), and the number at `b` below `M`: the number at `o` is below `M` and
its product with `R = 2^(64 n)` is congruent to the product of the numbers
at `a` and `b` modulo `M`. Only the function's own bytes and the result's may
change. The working space's address and length, the width and the offsets
are public; the numbers, the modulus among them, are secret. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen n mo inv s o a b m =>
      let nb := 8 * n.toNat
      let sb := scratchBytes n.toNat
      let M := numAt m ws mo.toNat nb
      let fits (x k : Nat) := x + k ≤ 8 * wsLen.toNat
      0 < n.toNat ∧ fits mo.toNat nb ∧ fits inv.toNat 4 ∧ fits s.toNat sb ∧
        fits o.toNat nb ∧ fits a.toNat nb ∧ fits b.toNat nb ∧
        Apart mo.toNat nb (s.toNat, sb) ∧ Apart inv.toNat 4 (s.toNat, sb) ∧
        Apart o.toNat nb (s.toNat, sb) ∧ Apart a.toNat nb (s.toNat, sb) ∧
        Apart b.toNat nb (s.toNat, sb) ∧
        Apart o.toNat nb (mo.toNat, nb) ∧ Apart o.toNat nb (inv.toNat, 4) ∧
        (M * numAt m ws inv.toNat 4 + 1) % 2 ^ 32 = 0 ∧ numAt m ws b.toNat nb < M)
    (post := fun ws wsLen n mo _inv s o a b m m' _ =>
      let nb := 8 * n.toNat
      let M := numAt m ws mo.toNat nb
      numAt m' ws o.toNat nb < M ∧
        numAt m' ws o.toNat nb * 2 ^ (64 * n.toNat) % M =
          numAt m ws a.toNat nb * numAt m ws b.toNat nb % M ∧
        Keeps ws wsLen.toNat [(s.toNat, scratchBytes n.toNat), (o.toNat, nb)] m m')
    (stack := stack)

end VG.Proof.Rsa.MontMul
