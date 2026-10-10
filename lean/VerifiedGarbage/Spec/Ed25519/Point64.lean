import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.TCB.Artifact

/-!
# Ed25519's point doubling and addition in radix `2^64`, as functions

**Trusted** (as every file in `Spec/`). The contracts of four functions on
points of edwards25519 in extended coordinates (`Point`), each coordinate
four 64-bit words, so that the Ed25519 code that keeps points this way (the
x86-64 code) can call one copy of each operation instead of repeating it at
every use:

* `vg_ed25519_r64_double_ext`: the double `[2]p`, by RFC 8032's doubling
  formula (§5.1.4, `pointDouble`);
* `vg_ed25519_r64_double_proj`: the same, but for `T`, which it does not
  compute: the projective coordinates `X, Y, Z` of the double;
* `vg_ed25519_r64_add_cached_ext`: the sum `p + q`, by the specification's
  complete addition formula (`pointAdd`), for `q` given in the cached form
  `[Y - X, Y + X, 2dT, 2Z]` (`cache`), which a table of points to add keeps;
* `vg_ed25519_r64_add_cached_proj`: the same, but for `T`.

A doubling or an addition that only a doubling (or a comparison) follows need
not compute `T`, which only an addition reads.

They are not algorithms of a standard but the arithmetic Ed25519 is built
from, in the representation that code keeps points in: what they compute is
stated on the coordinates as elements of `GF(p)`, `p = 2^255 - 19`.

A coordinate is 32 bytes, a little-endian number below `2^256`, standing for
its residue modulo `p` (`elemAt`): any 32 bytes are a coordinate. A point is
four coordinates, `X, Y, Z, T`, at consecutive offsets (`pointAt`). The
points live in Ed25519's working space `ws` of 8192 bytes (`[u64; 1024]`),
at fixed offsets, where that code keeps the operands: `p` at byte 64 (`pAt`),
`q`'s cached form at byte 192 (`qAt`); the result replaces `p`. Bytes 320 to
575 of `ws` are the functions' own working space. On return they are
unspecified and may hold intermediate values; every other byte of `ws` keeps
its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

namespace VG.Spec.Ed25519.Point64

open X25519 (P Fe)

/-- The doubling formula of RFC 8032, §5.1.4, in its stated order: the
double `[2]p` of a point in extended coordinates, which does not read `p.T`. -/
def pointDouble (p : Point) : Point :=
  let a := p.X * p.X
  let b := p.Y * p.Y
  let c := 2 * (p.Z * p.Z)
  let e := 2 * (p.X * p.Y)
  let g := b - a
  let f := c - g
  let h := a + b
  ⟨e * f, g * h, f * g, e * h⟩

/-- The cached form of `q`, `[Y - X, Y + X, 2dT, 2Z]`: the factors of `q` in
`pointAdd`'s products. -/
def cache (q : Point) : Point := ⟨q.Y - q.X, q.Y + q.X, q.T * 2 * d, q.Z * 2⟩

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of a coordinate. -/
def elemBytes : Nat := 32

/-- Where the first point, and the result, is. -/
def pAt : Nat := 64

/-- Where the second point's cached form is. -/
def qAt : Nat := 192

/-- Where the functions' own working space starts. -/
def ownAt : Nat := 320

/-- Where the functions' own working space ends. -/
def ownEnd : Nat := 576

/-- The coordinate at byte offset `o` of the working space `ws`: its 32
bytes, little-endian, modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe :=
  Fin.ofNat P (m.read (ws + BitVec.ofNat 64 o) elemBytes).toNat

/-- The point at byte offset `o`: its coordinates `X, Y, Z, T` at `o`,
`o + 32`, `o + 64` and `o + 96`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Point :=
  ⟨elemAt m ws o, elemAt m ws (o + elemBytes), elemAt m ws (o + 2 * elemBytes),
    elemAt m ws (o + 3 * elemBytes)⟩

/-- The point at `o` is `r`: all four coordinates if `ext`, else `X, Y, Z`. -/
def PointIs (ext : Bool) (m : Mem) (ws : Addr) (o : Nat) (r : Point) : Prop :=
  if ext then pointAt m ws o = r
  else elemAt m ws o = r.X ∧ elemAt m ws (o + elemBytes) = r.Y ∧
    elemAt m ws (o + 2 * elemBytes) = r.Z

/-- Every byte of `ws` but those of the result (bytes 64 to 191) and of the
functions' own working space (bytes 320 to 575) keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < pAt ∨ pAt + 4 * elemBytes ≤ i) → (i < ownAt ∨ ownEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pointDouble`: the point at `pAt` becomes its double (but for `T`, unless
`ext`). -/
def doubleContract {I : ISA} (A : Abi I) (ext : Bool) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun _ _ => True)
    (post := fun ws m m' _ =>
      PointIs ext m' ws pAt (pointDouble (pointAt m ws pAt)) ∧ Keeps ws m m')
    (stack := stack)

/-- `pointAdd`: for every point `q` whose cached form is at `qAt`, the point at
`pAt` becomes the sum of it and `q` (but for `T`, unless `ext`). -/
def addCachedContract {I : ISA} (A : Abi I) (ext : Bool) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun _ _ => True)
    (post := fun ws m m' _ =>
      (∀ q, pointAt m ws qAt = cache q → PointIs ext m' ws pAt (pointAdd (pointAt m ws pAt) q)) ∧
        Keeps ws m m')
    (stack := stack)

/-- The Rust module of the functions. -/
def module : String := "ed25519_r64"

/-- What every function's documentation says of its elements. -/
def elemDoc : String :=
  "A point is four coordinates `X, Y, Z, T` of 32 bytes each, consecutive; a coordinate is a \
    little-endian number below `2^256` standing for its residue modulo `p = 2^255 - 19`. Every \
    byte of `ws` but the result's and the function's own working space (bytes 320 to 575) \
    keeps its value."

/-- What the functions that do not compute `T` say of it. -/
def projDoc : String :=
  " It does not compute the result's `T`, which only an addition reads: the 32 bytes at byte \
    160 of `ws` are unspecified on return."

/-- What every function requires. -/
def safety : List String :=
  ["Bytes 320 to 575 of `ws` are unspecified on return and may hold intermediate values, \
      which the caller must destroy if they are secret."]

/-- What the doublings' documentation says they compute. -/
def doubleSummary : String :=
  "Point doubling on edwards25519: replaces the point at byte 64 of the working space `ws` \
    with its double, by RFC 8032's doubling formula in extended coordinates (§5.1.4). "

/-- What the additions' documentation says they compute. -/
def addSummary : String :=
  "Point addition on edwards25519: replaces the point at byte 64 of the working space `ws` \
    with its sum with the point `q` whose cached form, `[Y - X, Y + X, 2dT, 2Z]`, is at byte \
    192, by RFC 8032's complete addition formula in extended coordinates. "

/-- `vg_ed25519_r64_double_ext` on every target. -/
def doubleExtApi : Api where
  module := module
  name := "vg_ed25519_r64_double_ext"
  sig := sig
  contracts := some fun A stack => doubleContract A true stack
  summary := doubleSummary ++ elemDoc ++ "\n\n\
    Contract: `doubleContract` (`ext := true`) of `VG.Spec.Ed25519.Point64`. Constant time: \
    only the pointer may affect timing."
  safety := safety

/-- `vg_ed25519_r64_double_proj` on every target. -/
def doubleProjApi : Api where
  module := module
  name := "vg_ed25519_r64_double_proj"
  sig := sig
  contracts := some fun A stack => doubleContract A false stack
  summary := doubleSummary ++ elemDoc ++ projDoc ++ "\n\n\
    Contract: `doubleContract` (`ext := false`) of `VG.Spec.Ed25519.Point64`. Constant time: \
    only the pointer may affect timing."
  safety := safety

/-- `vg_ed25519_r64_add_cached_ext` on every target. -/
def addCachedExtApi : Api where
  module := module
  name := "vg_ed25519_r64_add_cached_ext"
  sig := sig
  contracts := some fun A stack => addCachedContract A true stack
  summary := addSummary ++ elemDoc ++ "\n\n\
    Contract: `addCachedContract` (`ext := true`) of `VG.Spec.Ed25519.Point64`. Constant time: \
    only the pointer may affect timing."
  safety := safety

/-- `vg_ed25519_r64_add_cached_proj` on every target. -/
def addCachedProjApi : Api where
  module := module
  name := "vg_ed25519_r64_add_cached_proj"
  sig := sig
  contracts := some fun A stack => addCachedContract A false stack
  summary := addSummary ++ elemDoc ++ projDoc ++ "\n\n\
    Contract: `addCachedContract` (`ext := false`) of `VG.Spec.Ed25519.Point64`. Constant \
    time: only the pointer may affect timing."
  safety := safety

end VG.Spec.Ed25519.Point64
