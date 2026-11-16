module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: the constants of the NTT in 16-bit lanes

The NTTs of `Ntt16/` compute on eight coefficients at a time, in the 16-bit
lanes of AdvSIMD registers, as signed integers. A product `a · z mod q`, for
`|a| < 2¹⁵` and a zeta `z < q`, is `r = a · z - t · q` with
`t = sqrdmulh(a, z')`, `z' = round(z · 2¹⁵ / q)` (`tw`): `t` is `a · z / q`
within `1/2 + |a| / 2¹⁶ < 1`, so `|r| < q`, and `r` is computed modulo `2¹⁶`.

The zetas of the layers with `len = 16, 8, 4, 2` are a table of 256
halfwords (`tableHalves`): for block `b` of 32 coefficients,
`Zs = (ζ_{8+b}, ζ_{16+2b}, ζ_{17+2b}, 0, ζ_{32+4b} … ζ_{35+4b})`, its `tw`,
`Z₇ = (ζ_{64+8b} … ζ_{71+8b})` and its `tw` (`blockHalves`).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

open VG.AArch64 VG.Impl.MlKem.AArch64

/-- `round(z · 2¹⁵ / q)`, for `z < q`. -/
def tw (z : Nat) : Nat := (z * 2 ^ 16 + 3329) / (2 * 3329)

/-- `ζ_k`. -/
def zeta (k : Nat) : Nat := zetaTable.getD k 0

/-- The 32 halfwords of block `b`'s zetas: `Zs`, its `tw`, `Z₇`, its `tw`. -/
def blockHalves (b : Nat) : List Nat :=
  let zs := [zeta (8 + b), zeta (16 + 2 * b), zeta (17 + 2 * b), 0] ++
    (List.range 4).map fun j => zeta (32 + 4 * b + j)
  let z7 := (List.range 8).map fun j => zeta (64 + 8 * b + j)
  zs ++ zs.map tw ++ z7 ++ z7.map tw

/-- The 256 halfwords of the table of the layers with `len = 16, 8, 4, 2`. -/
def tableHalves : List Nat := (List.range 8).flatMap blockHalves

end VG.Impl.MlKem.AArch64.Ntt16
