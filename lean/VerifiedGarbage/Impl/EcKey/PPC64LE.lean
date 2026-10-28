module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-!
# Elliptic curve public keys on PPC64LE

`vg_ec_<curve>_public_key(out, d, scratch) -> r3` (ELFv2: the arguments in
`r3`–`r5`), for a curve of `n` 64-bit words, from the code of ECDSA's
signature (`Impl/Ecdsa/PPC64LE.lean`), as on 32-bit ARM
(`Impl/EcKey/Arm.lean`):

1. the signature's code up to `Z^(p-2)`, with its setup reading `k`, `d`
   and the hash all from `d` (`Args.publicKey`): its tables of bits,
   `Q = [d]G` by its ladder, and its power;
2. `x = X Z^(p-2)` and `y = Y Z^(p-2)`, each left Montgomery's form by a
   multiplication by 1;
3. the flag, `d` in `[1, n-1]` and `Z ≠ 0`, as a mask, selects `04 ‖ x ‖ y`
   or zeros for `out` (big-endian, through `r14`, where the setup keeps it),
   and is returned as 0 or 1.

`Z = 0` iff `Q = O`, which the flag rejects as the specification does
(it cannot happen for `d` in `[1, n-1]`, as `G` has the prime order `n`).
Everything is computed whatever the flag, and only the pointers may affect
timing.
-/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass
open VG.Impl.Ecdsa.PPC64LE

/-! Slots of the signature's layout that the public key does not otherwise use. -/

/-- `Y Z^(p-2)`, in Montgomery form. -/
def YM : Nat := RM
/-- `y`. -/
def Y : Nat := SS

/-- The public key's arguments: `(out, d, scratch)`, with `k` and the hash
both `d`, and `scratch` in `r5`. -/
abbrev Args.publicKey : Args := ⟨.r4, .r4, .r4, .r5, none⟩

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The signature's code up to `Z^(p-2)`, with the public key's arguments. -/
def upToPow : Prog isa :=
  .seq (.block (c.setupWith Args.publicKey)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq c.gen <|
  .seq (pow c.powP c.SP) (.block [])

/-- `04 ‖ x ‖ y` (or zeros), from the slots `x` and `y`, to `out` (in `r14`),
the flag's low bit to `r3`, and the callee-saved registers restored. -/
def finishWith (x y : Nat) : List Instr :=
  ([.load .d .r10 wb (c.sl FLAG), .li .r4 4, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0] : List Instr) ++
  storeBytes c.C.len c.n .r14 1 (c.sl x) ++ storeBytes c.C.len c.n .r14 (1 + c.C.len) (c.sl y) ++
  ([.li .r4 1, .logic .and .r4 .r10 .r4] : List Instr) ++ Impl.Ecdsa.PPC64LE.Cfg.restore ++ [mov .r3 .r4]

/-- `04 ‖ x ‖ y` (or zeros) to `out`, from `X` and `Y`. -/
def finish : List Instr := finishWith c X Y

/-- `x = X Z⁻¹` and `y = Y Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery
form, the checks of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    mulCall c.SP (c.sl YM) (c.sl RY) (c.sl ACC),
    mulCall c.SP (c.sl Y) (c.sl YM) (c.sl ONE),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-- `vg_ec_<curve>_public_key`. -/
def publicKey : Prog isa := .seq (upToPow c) (middle c)

end Cfg

end VG.Impl.EcKey.PPC64LE
