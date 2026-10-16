module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast

/-!
# AES-GCM on AArch64: the key context with prepared powers

`vg_aes_gcm_init_prepared(key = x0, key_len = x1, ctx = x2, scratch = x3)`
writes the key context of `vg_aes_gcm_init`, then the 48 powers
`H'ᵏ = Hᵏ · x⁻¹` of `Spec.Gcm.PreparedPowersRepr`, which are exactly the
keys `vg_aes_gcm_*_aes` multiply by (`tReg k` of `Impl.Gcm.AArch64.Pmull`):
`preparedPower` shifts a block left by one bit, reducing, which multiplies
it by `x⁻¹`. The register value of such a key, stored with `str q`, is its
little-endian storage.

`H'` is computed as `vg_ghash_aes` computes it (`Fast.key`) and stored at
`ctx + 272`. Then each of twelve iterations writes four powers from two
it reads: with `q = ctx + 256 + 32i` and `p = ctx + 256 + 64i`, the powers
`H'²ⁱ⁺¹` at `q + 16` and `H'²ⁱ⁺²` at `q`, squared, give `H'⁴ⁱ⁺²` and
`H'⁴ⁱ⁺⁴` (at `p` and `p + 32`), and `H'⁴ⁱ⁺¹` and `H'⁴ⁱ⁺³` (at `p + 16`
and `p + 48`) are `H'⁴ⁱ` and `H'⁴ⁱ⁺²`, each times `H'`. `H'⁴ⁱ` is kept from
the iteration before, and is `x⁻¹` (`H'⁰`) at first. The first iteration
reads `H'²` at `ctx + 256` after storing it. So only one product a
iteration waits for the previous iteration.

It needs PMULL, so only the variants with it have it. Every branch and
address depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.Prepared

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (tReg sReg mul)

/-! Registers: `v16` and `v24` `H'` and with its halves swapped
(`Fast.key`), `v1` the reduction constant, `v19` a power loaded and `v20`
it with its halves swapped, `v21`/`v22` an even power (swapped / as it
is), `v23`/`v26` an odd one, `v18` `H'⁴ⁱ` with its halves swapped. -/

abbrev PL : VReg := .v19
abbrev PS : VReg := .v20
abbrev ES : VReg := .v21
abbrev ET : VReg := .v22
abbrev OS : VReg := .v23
abbrev OT : VReg := .v26
abbrev KS : VReg := .v18

/-- The power at `[x9, #off]`, as it is and with its halves swapped. -/
def ld (off : Nat) : List Instr := [.ldrq PL .x9 off, .vop (.ext PS PL PL 8)]

/-- `d ← (PL)²`, with its halves swapped, and `dt` as it is. -/
def sq (d dt : VReg) : List Instr := mul d PS PS PL ++ ([.vop (.ext dt d d 8)] : List Instr)

/-- `d ← a · H'`, with its halves swapped (`a` too), and `dt` as it is. -/
def byH (d dt a : VReg) : List Instr := mul d a (sReg 1) (tReg 1) ++ ([.vop (.ext dt d d 8)] : List Instr)

/-- One iteration: four powers from two. -/
def step : List Instr :=
  ld 16 ++ sq ES ET ++ byH OS OT KS ++ ([.strq ET .x10 0, .strq OT .x10 16] : List Instr) ++
  ld 0 ++ sq KS ET ++ byH OS OT ES ++ ([.strq ET .x10 32, .strq OT .x10 48,
    .addImm .x .x9 .x9 32, .addImm .x .x10 .x10 64, .subImm .x .x11 .x11 1] : List Instr)

/-- `H'` from `H` at `ctx + 240`, stored at `ctx + 272`; `x⁻¹` with its
halves swapped (`0xc2 · 2⁵⁶` and 1); the pointers and the count. -/
def setup : List Instr :=
  ([.addImm .x .x0 .x21 240] : List Instr) ++ Fast.key ++
  ([.strq (tReg 1) .x21 272, .movz .x .x6 0xc200 3, .vop (.ins .d2 KS 0 .x6), .movz .x .x6 1 0,
    .vop (.ins .d2 KS 1 .x6), .addImm .x .x9 .x21 256, .addImm .x .x10 .x21 256, .movz .x .x11 12 0] :
    List Instr)

/-- The 48 powers, after the hash subkey. -/
def powers : Prog isa := .seq (.block setup) (.loop (.block step) (.nonzero .x .x11))

/-- `vg_aes_gcm_init_prepared`. -/
def init (c : Callees) : Prog isa := initWith c (.seq powers (.block restore))

end VG.Impl.AesGcm.AArch64.Prepared
