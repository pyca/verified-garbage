import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# Elliptic curve public keys on AArch64

`vg_ec_<curve>_public_key(out = x0, d = x1, scratch = x2) -> w0`, for a
curve of `n` 64-bit words, from the code of ECDSA's signature
(`Impl/Ecdsa/AArch64.lean`), as on x86-64 (`Impl/EcKey/X86_64.lean`):

1. `scratch` to `x4`, and `d`'s pointer to `x3` and `x2` too, as the
   signature's arguments `k` and `digest`; then the signature's code up to
   `Z^(p-2)`, unchanged: its setup (which reads `d` into the slots of `k`,
   `d` and the hash), its tables of bits, `Q = [d]G` by its ladder, and its
   power;
2. `x = X Z^(p-2)` and `y = Y Z^(p-2)`, each left Montgomery's form by a
   multiplication by 1;
3. the flag, `d` in `[1, n-1]` and `Z ≠ 0`, as a mask, selects `04 ‖ x ‖ y`
   or zeros for `out` (big-endian, from `out + 1`, which `x6` holds, as an
   8-byte store's offset is a multiple of 8), and is returned as 0 or 1.

`Z = 0` iff `Q = O`, which the flag rejects as the specification does
(it cannot happen for `d` in `[1, n-1]`, as `G` has the prime order `n`).
Everything is computed whatever the flag, and only the pointers may affect
timing.
-/

namespace VG.Impl.EcKey.AArch64

open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64

/-! Slots of the signature's layout that the public key does not otherwise use. -/

/-- `Y Z^(p-2)`, in Montgomery form. -/
def YM : Nat := RM
/-- `y`. -/
def Y : Nat := SS

namespace Cfg

variable (c : Impl.Ecdsa.AArch64.Cfg)

/-- `scratch` to `x4`, `d`'s pointer to `x3` and `x2`: the signature's
arguments, with `k` and the hash both `d`. -/
def args : List Instr := [.addImm .x .x4 .x2 0, .addImm .x .x3 .x1 0, .addImm .x .x2 .x1 0]

/-- The signature's code up to `Z^(p-2)`. -/
def upToPow : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (TCombCfg.comb c.combCfg) <|
  .seq c.pPow (.block [])

/-- `04 ‖ x ‖ y` (or zeros) to `out`, `x19` and `x20` restored, and the
flag's low bit to `x0`. -/
def finish : List Instr :=
  [ld .x3 (c.sl FLAG), .movz .x .x1 4 0, .logic .and .x .x1 .x1 .x3, .strb .x1 .x20 0,
    .addImm .x .x6 .x20 1] ++
  storeBE c.n .x6 0 (c.sl X) ++ storeBE c.n .x6 (8 * c.n) (c.sl Y) ++
  Impl.Ecdsa.AArch64.Cfg.saved.map (fun (r, d) => ld r d) ++
  [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]

/-- `x = X Z⁻¹` and `y = Y Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery
form, the checks of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  blocks [Mont.AArch64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.AArch64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.AArch64.mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC),
    Mont.AArch64.mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE),
    c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c]

/-- `vg_ec_<curve>_public_key`. -/
def publicKey : Prog isa :=
  .seq (.block args) (.seq (upToPow c) (middle c))

end Cfg

end VG.Impl.EcKey.AArch64
