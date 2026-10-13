module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-!
# Elliptic curve public keys on 32-bit ARM

`vg_ec_<curve>_public_key(out, d, scratch) -> r0` (AAPCS: `out` and `d` in
`r0` and `r1`, `scratch` in `r2`), for a curve of `n` 64-bit words, from
the code of ECDSA's signature (`Impl/Ecdsa/Arm.lean`), as on x86
(`Impl/EcKey/X86.lean`):

1. the signature's code up to `Z^(p-2)`, with its setup reading `k`, `d`
   and the hash all from `d` (`Args.publicKey`): its tables of bits,
   `Q = [d]G` by its ladder, and its power;
2. `x = X Z^(p-2)` and `y = Y Z^(p-2)`, each left Montgomery's form by a
   multiplication by 1;
3. the flag, `d` in `[1, n-1]` and `Z ≠ 0`, as a mask, selects `04 ‖ x ‖ y`
   or zeros for `out` (big-endian, through `lr`, where the setup keeps it),
   and is returned as 0 or 1.

`Z = 0` iff `Q = O`, which the flag rejects as the specification does
(it cannot happen for `d` in `[1, n-1]`, as `G` has the prime order `n`).
Everything is computed whatever the flag, and only the pointers may affect
timing.
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm

/-! Slots of the signature's layout that the public key does not otherwise use. -/

/-- `Y Z^(p-2)`, in Montgomery form. -/
def YM : Nat := RM
/-- `y`. -/
def Y : Nat := SS

/-- The public key's arguments: `(out, d, scratch)`, with `k` and the hash
both `d`, and `scratch` in `r2`. -/
abbrev Args.publicKey : Args := ⟨.r1, .r1, .r1, some .r2, none⟩

namespace Cfg

variable (c : Impl.Ecdsa.Arm.Cfg)

/-- The signature's code up to `Z^(p-2)`, with the public key's arguments. -/
def upToPow : Prog isa :=
  .seq (.block (c.setupWith Args.publicKey)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (Point.ladderP c.ladderCfg c.SP) <|
  .seq (pow c.powP c.SP) (.block [])

/-- `04 ‖ x ‖ y` (or zeros) to `out` (in `lr`), the flag's low bit to `r0`,
and the callee-saved registers restored. -/
def finish : List Instr :=
  ([.ldr .r10 wb (c.sl FLAG), .mov .r4 (.imm 4), .dp .and .r4 .r4 (.reg .r10), .strb .r4 .lr 0] : List Instr) ++
  storeBytes c.C.len c.n .lr 1 (c.sl X) ++ storeBytes c.C.len c.n .lr (1 + c.C.len) (c.sl Y) ++
  ([.dp .and .r0 .r10 (.imm 1)] : List Instr) ++ Impl.Ecdsa.Arm.Cfg.restore

/-- `x = X Z⁻¹` and `y = Y Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery
form, the checks of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.mulCall c.SP (c.sl YM) (c.sl RY) (c.sl ACC),
    Mont.mulCall c.SP (c.sl Y) (c.sl YM) (c.sl ONE),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-- `vg_ec_<curve>_public_key`. -/
def publicKey : Prog isa := .seq (upToPow c) (middle c)

end Cfg

end VG.Impl.EcKey.Arm
