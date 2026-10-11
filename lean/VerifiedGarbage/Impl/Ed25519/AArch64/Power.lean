module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Word
public import VerifiedGarbage.Spec.X25519.Field64

/-!
# The shared addition chain for inversion and square-root recovery

`power250` leaves `z^(2^250 - 1)` and `z^11` in `T1` and `T0`, for `z` in `Z2`:
the offsets of `vg_gf25519_r64_pow250` (`Spec/X25519/Field64.lean`; AAPCS64:
`ws` in `x0`), which runs it as a function (`powFn`), keeping the callee-saved
registers it writes (`x19`, the squarings' counter, and `x20`–`x24`) in lanes
of `v16`–`v18`, which are not callee-saved, so that it needs no stack.
Inversion (`invert`, `z^(p-2)`) and decoding's square root (`rootPower`,
`z^((p-5)/8)`) call it (`powCall`, with the return address kept in a lane of
`v31`, which it does not write) and finish with a few squarings and a product.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def Z2 : Nat := 128
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608

def sqn (o a n : Nat) : Prog isa :=
  .seq (.block (fieldSqr o a ++ const64 .x19 (BitVec.ofNat 64 (n - 1))))
    (.loop (.block (fieldSqr o o ++ [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

/-- From z in Z2, leave z^(2^250 - 1) in T1 and z^11 in T0. -/
def power250 : Prog isa :=
  .seq (.block (fieldSqr T0 Z2)) <|
  .seq (.block (fieldSqr T1 T0 ++ fieldSqr T1 T1)) <|
  .seq (.block (fieldMul T1 Z2 T1 ++ fieldMul T0 T0 T1 ++
    fieldSqr T2 T0 ++ fieldMul T1 T1 T2)) <|
  .seq (sqn T2 T1 5) <| .seq (.block (fieldMul T1 T2 T1)) <|
  .seq (sqn T2 T1 10) <| .seq (.block (fieldMul T2 T2 T1)) <|
  .seq (sqn T3 T2 20) <| .seq (.block (fieldMul T2 T3 T2)) <|
  .seq (sqn T2 T2 10) <| .seq (.block (fieldMul T1 T2 T1)) <|
  .seq (sqn T2 T1 50) <| .seq (.block (fieldMul T2 T2 T1)) <|
  .seq (sqn T3 T2 100) <| .seq (.block (fieldMul T2 T3 T2)) <|
  .seq (sqn T2 T2 50) (.block (fieldMul T1 T2 T1))

/-- Where `vg_gf25519_r64_pow250` keeps the callee-saved registers it writes. -/
def powKept : List (Reg × VReg × Nat) :=
  [(.x19, .v16, 0), (.x20, .v16, 1), (.x21, .v17, 0), (.x22, .v17, 1), (.x23, .v18, 0),
    (.x24, .v18, 1)]

/-- `vg_gf25519_r64_pow250`: `power250`, the registers it writes kept in lanes. -/
def powFn : Prog isa :=
  .seq (.block (powKept.map fun k => .vop (.ins .d2 k.2.1 k.2.2 k.1)))
    (.seq power250 (.block (powKept.map fun k => .umov .x k.1 k.2.1 k.2.2)))

/-- A call of `vg_gf25519_r64_pow250` (`ws` in `x0`), with the return address kept in `v31`. -/
def powCall : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v31 0 .x30)]) <|
    .seq (.call Spec.X25519.Field64.pow250Api.name powFn) (.block [.umov .x .x30 .v31 0])

def invert : Prog isa := .seq powCall (.seq (sqn T1 T1 5) (.block (fieldMul T1 T1 T0)))

def rootPower : Prog isa := .seq powCall (.seq (sqn T1 T1 2) (.block (fieldMul T1 T1 Z2)))

end VG.Impl.Ed25519.AArch64
