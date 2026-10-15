module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
public import VerifiedGarbage.Impl.Ed25519.AArch64.Field
public import VerifiedGarbage.Spec.X25519

/-!
# X25519 on AArch64: the inversion by divsteps

`[slot 15] = [slot 2]^(p - 2)` for `p = 2²⁵⁵ - 19`, by the short Weierstrass
curves' inversion (`Weierstrass.AArch64.InvCfg.inv`: Bernstein–Yang divsteps
in ten batches of 59, then a Montgomery multiplication by a constant), in
place of the ref10 addition chain's 254 squarings and 11 multiplications.

That inversion works in Montgomery form (`R = 2²⁵⁶`): `z` goes in as
`z R mod p` (a Montgomery product with `R² mod p`, which also reduces it
below `p`), and the result, `z^(p - 2) R`, comes out by a Montgomery product
with `1`. The modulus, `R² mod p` and `1` are written first; the output
pointer `x1`, which the products use, is kept in the working space.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Invert

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ed25519.AArch64 (offset)

/-- The inversion's table area (`9 · 4` words). -/
def TBL : Nat := 2304
/-- `z R mod p`, the inversion's input. -/
def BASE : Nat := TBL + 288
/-- `z^(p - 2) R mod p`, its result. -/
def ACC : Nat := BASE + 32
/-- `R² mod p = 38² = 1444` (`2²⁵⁶ ≡ 38`). -/
def R2 : Nat := ACC + 32
/-- `1`. -/
def ONE : Nat := R2 + 32
/-- The output pointer `x1`. -/
def SX1 : Nat := ONE + 32

/-- `p` for the Montgomery arithmetic: at `moAt 4`, its temporary area below it. -/
def M : Mod := Weierstrass.AArch64.Mont.mod 4 Spec.X25519.P

/-- The inversion's configuration. -/
def cfg : InvCfg := InvCfg.ofMod M ACC BASE TBL Spec.X25519.P

/-- `[o] = v` (four words), through `x2`. -/
def storeConst (o v : Nat) : List Instr :=
  (List.range 4).flatMap fun i => const64 .x2 (BitVec.ofNat 64 (v >>> (64 * i))) ++ [st .x2 (o + 8 * i)]

/-- The constants, and `[BASE] = z R mod p`. -/
def pre : List Instr :=
  [st .x1 SX1] ++ storeConst M.mo Spec.X25519.P ++ storeConst R2 1444 ++
  storeConst ONE 1 ++ Mont.AArch64.mul M BASE (offset 2) R2

/-- `[slot 15] = z^(p - 2) mod p`, and `x1` back. -/
def post : List Instr := Mont.AArch64.mul M (offset 15) ACC ONE ++ [ld .x1 SX1]

/-- `[slot 15] = [slot 2]^(p - 2) mod p`. -/
def invert : Prog isa := .seq (.block pre) (.seq cfg.inv (.block post))

end VG.Impl.X25519.AArch64.Invert
