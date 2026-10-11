import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Spec.Ed25519.Point64

/-!
# Ed25519's point doubling and affine addition on AArch64, as functions

`vg_ed25519_r64_double_ext(ws)` and `vg_ed25519_r64_add_affine_ext(ws)`
(`Spec/Ed25519/Point64.lean`; AAPCS64: `ws` in `x0`) run field programs on
the slots the base-point comb keeps its operands in: the point in slots 0–3
(byte 64), the affine entry's `[Y - X, Y + X, 2dT]` in slots 4–6 (byte 192),
and their temporaries in slots 8–15 (bytes 320–575), the functions' own
working space. Each keeps the callee-saved registers the field products
write (`x20`–`x24`) in lanes of `v16`–`v18`, which are not callee-saved, so
that it needs no stack, as `vg_gf25519_r64_pow250` does (`powFn`); a call
keeps the return address in a lane of `v31`, which neither writes.

Every address is `ws` plus a constant, and there are no branches: only the
pointer, which is public, may affect timing.
-/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- RFC 8032's doubling (§5.1.4) of the point in slots 0–3, in place: `a = X²`, `b = Y²`,
`c = 2Z²`, `(X + Y)²`, `h = a + b`, `e = h - (X + Y)²`, `g = a - b`, `f = c + g`, and
`(ef, gh, fg, eh)`. Slots 8–15 are temporary. -/
def doubleRfcOps : List FieldOp := [
  .sqr 8 0, .sqr 9 1, .sqr 10 2, .add 10 10 10, .add 11 0 1, .sqr 11 11,
  .add 12 8 9, .sub 13 12 11, .sub 14 8 9, .add 15 10 14,
  .mul 0 13 15, .mul 1 14 12, .mul 2 15 14, .mul 3 13 12]

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of a point with `Z = 1`,
so its `2Z` is `2` and `Z₁ · 2Z₂` is `Z₁ + Z₁`) to the point in slots 0–3, in place:
`a = (Y₁ - X₁)(Y₂ - X₂)`, `b = (Y₁ + X₁)(Y₂ + X₂)`, `c = T₁ · 2dT₂`, `dd = 2Z₁`,
`h = b + a`, `e = b - a`, `g = dd + c`, `f = dd - c`, and `(ef, gh, fg, eh)`. Slots 8–12 are
temporary. -/
def addAffineOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6, .add 11 2 2,
  .add 12 9 8, .sub 8 9 8, .add 9 11 10, .sub 10 11 10,
  .mul 0 8 10, .mul 1 9 12, .mul 2 10 9, .mul 3 8 12]

namespace Point64

/-- Where the functions keep the callee-saved registers the field products write. -/
def kept : List (Reg × VReg × Nat) :=
  [(.x20, .v16, 0), (.x21, .v16, 1), (.x22, .v17, 0), (.x23, .v17, 1), (.x24, .v18, 0)]

/-- The field program `ops` as a function, the registers it writes kept in lanes. -/
def fn (ops : List FieldOp) : Prog isa :=
  .seq (.block (kept.map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)))
    (.seq (.block (fieldCode ops)) (.block (kept.map fun k => .umov .x k.1 k.2.1 k.2.2)))

/-- `vg_ed25519_r64_double_ext`. -/
def doubleFn : Prog isa := fn doubleRfcOps

/-- `vg_ed25519_r64_add_affine_ext`. -/
def affFn : Prog isa := fn addAffineOps

/-- A call of `name` (`ws` in `x0`), with the return address kept in `v31`. -/
def call (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v31 0 .x30)]) <|
    .seq (.call name body) (.block [.umov .x .x30 .v31 0])

def doubleCall : Prog isa := call Spec.Ed25519.Point64.doubleExtApi.name doubleFn

def affCall : Prog isa := call Spec.Ed25519.Point64.addAffineExtApi.name affFn

end Point64

end VG.Impl.Ed25519.AArch64
