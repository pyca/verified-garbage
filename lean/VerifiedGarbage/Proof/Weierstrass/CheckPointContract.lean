module

public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-!
# The check of a public point, in a curve's working space, as an internal function

Not trusted: the contract of one function for
each curve of `curves` (P-192, P-224, P-256, secp256k1, P-384, P-521,
brainpoolP256r1, brainpoolP384r1 and brainpoolP512r1), on the working space where the code of the curve's ECDH
and ECDSA verification keeps the public point it checks, so that both can
call one copy of the check instead of repeating it:

* `vg_<curve>_check_point(ws)`: for the numbers `x` (slot 33) and `y`
  (slot 36) of the public point, ANDs into the flag (the 64-bit word at
  slot 44) the mask of `x < p`, `y < p` and `(x, y)` on the curve
  (`y² = x³ + a x + b` in `GF(p)`, `Weierstrass.onCurve`): the checks of
  `EcKey.decodePublicKey` (SP 800-56A §5.6.2.3.3, SEC 1 §3.2.2.1 steps 2
  and 3) on the decoded coordinates; writes `x` and `y` in Montgomery's form (slots 34 and 35); and
  writes the point the scalar multiplication takes (slots 38 and 43): the
  public point in Montgomery's form if the flag is set, else `G`'s
  coordinates, which the caller keeps at slots 8 and 9.

It is not an algorithm of a standard but a step of ECDH's and ECDSA
verification's: what it computes is stated on integers and on the curve of
`Spec/Weierstrass.lean` (its `p`, `a` and `b`), so that a caller's proof that
it checks the public key as its specification says follows from it.

The numbers are `k` 64-bit words, little-endian, at byte offsets of the
working space `ws` of 8192 bytes, in slots from byte 64 (`slot`), where the
code keeps them: the caller provides `p` (slot 0), `R² mod p` (slot 39), and
the curve's `a` and `b` in Montgomery's form (`a R mod p`, slot 6, and
`b R mod p`, slot 40), for `R = 2^(64 k)`. A number in Montgomery's form is
`x R mod p`, which stands for `x` (`Proof/Weierstrass/PointContract.lean`). The flag
is a mask, zero or all ones: the function keeps it a mask, set only if it was
and the point passes.

Slots 2, 37, 41 and 42, and the `64 k` bytes below byte 4096 (the own
working space of the functions of `Proof/Weierstrass/MontContract.lean`, which it
may call), are the function's own working space (`Own`); on return they are
unspecified. Every other byte of `ws` keeps its value but those of the
results (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time: it computes everything whatever the flag and the point.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/CheckPoint.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.CheckPoint

open Mont (wsBytes numAt)

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

namespace Curve

variable (C : Curve)

/-- Byte `i` is in the function's own working space: slot 2, 37, 41 or 42,
or the own working space of the functions of `Proof/Weierstrass/MontContract.lean`. -/
def Own (i : Nat) : Prop :=
  (∃ j ∈ [2, 37, 41, 42], C.slot j ≤ i ∧ i < C.slot j + 8 * C.k) ∨ (Mont.ownAt C.k ≤ i ∧ i < 4096)

/-- Byte `i` is one of a result's: of slots 34, 35, 38 and 43, or of the
flag's word. -/
def Out (i : Nat) : Prop :=
  (∃ j ∈ [34, 35, 38, 43], C.slot j ≤ i ∧ i < C.slot j + 8 * C.k) ∨ (C.flagAt ≤ i ∧ i < C.flagAt + 8)

/-- Every byte of `ws` but those of the own working space and of the
results keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → ¬ C.Out i → m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The number of `k` words at offset `o` of `ws`. -/
def num (ws : Addr) (m : Mem) (o : Nat) : Nat := numAt m ws (BitVec.ofNat 32 o) C.k

/-- The flag's word. -/
def flag (ws : Addr) (m : Mem) : BitVec 64 := m.read (ws + BitVec.ofNat 64 C.flagAt) 8

/-- The mask of `b`: all ones if it holds, else zero. -/
def mask (b : Prop) [Decidable b] : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- The point `(x, y)` passes: `x` and `y` are below `p`, and the point is on
the curve. -/
def Valid (x y : Nat) : Prop :=
  x < C.W.p ∧ y < C.W.p ∧ Spec.Weierstrass.onCurve C.W (.affine (Fin.ofNat C.W.p x) (Fin.ofNat C.W.p y)) = true

instance (x y : Nat) : Decidable (C.Valid x y) := by unfold Valid; infer_instance

/-- What the function requires: `p`, `R² mod p`, `a R mod p` and `b R mod p`
where the caller keeps them, and the flag a mask. -/
def pre (ws : Addr) (m : Mem) : Prop :=
  C.num ws m C.pAt = C.W.p ∧ C.num ws m C.r2At = C.R * C.R % C.W.p ∧
    C.num ws m C.aAt = C.W.a * C.R % C.W.p ∧ C.num ws m C.bAt = C.W.b * C.R % C.W.p ∧
    (C.flag ws m = 0 ∨ C.flag ws m = BitVec.allOnes 64)

/-- What it ensures, for the point `(x, y)` it reads: the flag `&=` the mask
of `Valid x y`; `x R mod p` and `y R mod p`; the public point in Montgomery's
form if the flag is set, else `G`'s coordinates as the caller keeps them; and
every other byte of `ws` but the own working space's kept. -/
def post (ws : Addr) (m m' : Mem) : Prop :=
  let x := C.num ws m C.xAt
  let y := C.num ws m C.yAt
  let f := C.flag ws m &&& mask (C.Valid x y)
  C.flag ws m' = f ∧
    C.num ws m' C.xmAt = x * C.R % C.W.p ∧ C.num ws m' C.ymAt = y * C.R % C.W.p ∧
    C.num ws m' C.pxAt = (if f = 0 then C.num ws m C.gxAt else x * C.R % C.W.p) ∧
    C.num ws m' C.pyAt = (if f = 0 then C.num ws m C.gyAt else y * C.R % C.W.p) ∧
    C.Keeps ws m m'

/-- `check_point`: the flag `&=` the mask of the public point's validity. -/
def checkContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.pre ws m) (post := fun ws m m' _ => C.post ws m m')
    (stack := stack)

end Curve

end VG.Impl.Weierstrass.CheckPoint
