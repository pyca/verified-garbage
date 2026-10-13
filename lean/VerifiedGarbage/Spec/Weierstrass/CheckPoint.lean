module

public import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# The check of a public point, in a curve's working space, as a function

**Trusted** (as every file in `Spec/`). The contract of one function for
each curve of `curves` (P-192, P-224, P-256, secp256k1, P-384 and P-521),
on the working space where the code of the curve's ECDH and ECDSA
verification keeps the public point it checks, so that both can call one
copy of the check instead of repeating it:

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
`x R mod p`, which stands for `x` (`Spec/Weierstrass/Point.lean`). The flag
is a mask, zero or all ones: the function keeps it a mask, set only if it was
and the point passes.

Slots 2, 37, 41 and 42, and the `64 k` bytes below byte 4096 (the own
working space of the functions of `Spec/Weierstrass/Mont.lean`, which it
may call), are the function's own working space (`Own`); on return they are
unspecified. Every other byte of `ws` keeps its value but those of the
results (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time: it computes everything whatever the flag and the point.
-/

@[expose] public section

namespace VG.Spec.Weierstrass.CheckPoint

open Mont (wsBytes numAt)

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- A curve whose check of a public point is a function: the curve `W` (its
prime `p` and coefficients `a` and `b`), its name (the function is
`vg_<curve>_check_point`, in the Rust module `<curve>_check_point`), the
count `k` of 64-bit words of a number, with `p < 2^(64 k)`, and how the
documentation names it. -/
structure Curve where
  W : Weierstrass.Curve
  curve : String
  k : Nat
  desc : String

namespace Curve

variable (C : Curve)

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where `p` is. -/
def pAt : Nat := C.slot 0

/-- Where `a R mod p` is. -/
def aAt : Nat := C.slot 6

/-- Where `G`'s coordinates, as the scalar multiplication takes them, are. -/
def gxAt : Nat := C.slot 8
def gyAt : Nat := C.slot 9

/-- Where the public point's `x` and `y` are. -/
def xAt : Nat := C.slot 33
def yAt : Nat := C.slot 36

/-- Where `x` and `y` in Montgomery's form go. -/
def xmAt : Nat := C.slot 34
def ymAt : Nat := C.slot 35

/-- Where the point the scalar multiplication takes goes. -/
def pxAt : Nat := C.slot 38
def pyAt : Nat := C.slot 43

/-- Where `R² mod p` is. -/
def r2At : Nat := C.slot 39

/-- Where `b R mod p` is. -/
def bAt : Nat := C.slot 40

/-- Where the flag is: its first 64-bit word. -/
def flagAt : Nat := C.slot 44

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * C.k)

/-- Byte `i` is in the function's own working space: slot 2, 37, 41 or 42,
or the own working space of the functions of `Spec/Weierstrass/Mont.lean`. -/
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
  x < C.W.p ∧ y < C.W.p ∧ Weierstrass.onCurve C.W (.affine (Fin.ofNat C.W.p x) (Fin.ofNat C.W.p y)) = true

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

/-! ## The function -/

/-- The Rust module of the curve's function. -/
def module : String := C.curve ++ "_check_point"

/-- Where the documentation says a range of bytes is. -/
def rangeDoc (o n : Nat) : String := s!"{o} to {o + n - 1}"

/-- Where the documentation says slot `i` is. -/
def slotDoc (i : Nat) : String := rangeDoc (C.slot i) (8 * C.k)

/-- What the documentation says the function's own working space is. -/
def ownDoc : String :=
  s!"Bytes {C.slotDoc 2}, {C.slotDoc 37}, {C.slotDoc 41}, {C.slotDoc 42} and \
    {rangeDoc (Mont.ownAt C.k) (Mont.ownBytes C.k)} of `ws`"

/-- `vg_<curve>_check_point` on every target. -/
def checkApi : Api where
  module := C.module
  name := s!"vg_{C.curve}_check_point"
  sig := sig
  contracts := some fun A stack => C.checkContract A stack
  summary := s!"The check of a public point `(x, y)` on {C.desc} (SEC 1 §3.2.2.1, steps 2 and \
    3): ANDs into the flag, the 64-bit word at byte {C.flagAt} of `ws`, the mask (all ones or \
    zero) of `x < p`, `y < p` and `y² = x³ + a x + b` modulo {C.desc}'s prime `p`. Numbers are \
    {C.k} 64-bit words (`{8 * C.k}` bytes), little-endian: the function reads `x` at byte \
    {C.xAt}, `y` at byte {C.yAt}, `p` at byte {C.pAt}, `R² mod p` at byte {C.r2At} and the \
    curve's `a R mod p` and `b R mod p` at bytes {C.aAt} and {C.bAt}, for `R = 2^{64 * C.k}`. It \
    writes `x R mod p` at bytes {C.slotDoc 34} and `y R mod p` at bytes {C.slotDoc 35}, and at \
    bytes {C.slotDoc 38} and {C.slotDoc 43} the same if the flag is set on return, else the \
    numbers at bytes {C.gxAt} and {C.gyAt}. {C.ownDoc} are the function's own working space; \
    every other byte of `ws` but the results' keeps its value. Constant time: only the pointer \
    may affect timing.\n\n\
    Contract: `checkContract` of `VG.Spec.Weierstrass.CheckPoint.Curve`."
  safety :=
    [s!"The {C.k} words at byte {C.pAt} of `ws` must be {C.desc}'s prime `p`, those at byte \
        {C.r2At} `R² mod p`, and those at bytes {C.aAt} and {C.bAt} the curve's `a R mod p` and \
        `b R mod p`.",
      s!"The flag, the 64-bit word at byte {C.flagAt} of `ws`, must be zero or all ones.",
      s!"{C.ownDoc} are unspecified on return and may hold intermediate values, which the caller \
        must destroy if they are secret."]

end Curve

/-! ## The curves -/

def p192 : Curve := { W := Spec.P192.curve, curve := "p192", k := 4, desc := "P-192" }
def p224 : Curve := { W := Spec.P224.curve, curve := "p224", k := 4, desc := "P-224" }
def p256 : Curve := { W := Spec.P256.curve, curve := "p256", k := 4, desc := "P-256" }
def secp256k1 : Curve := { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1" }
def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384" }
def p521 : Curve := { W := Spec.P521.curve, curve := "p521", k := 9, desc := "P-521" }

/-- Every curve. -/
def curves : List Curve := [p192, p224, p256, secp256k1, p384, p521]

end VG.Spec.Weierstrass.CheckPoint
