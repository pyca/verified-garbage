import VerifiedGarbage.Impl.Ecdsa.X86

/-!
# Elliptic curve public keys on x86 (32-bit)

`vg_ec_<curve>_public_key(out, d, scratch) -> eax` (cdecl: the arguments at
`[esp + 4]` to `[esp + 12]`), for a curve of `n` 64-bit words, from the code
of ECDSA's signature (`Impl/Ecdsa/X86.lean`), as on x86-64 and AArch64
(`Impl/EcKey/AArch64.lean`):

1. the signature's code up to `Z^(p-2)`, with its setup reading the working
   space from `scratch` and `k`, `d` and the hash all from `d`
   (`Args.publicKey`): its tables of bits, `Q = [d]G` by its ladder, and its
   power;
2. `x = X Z^(p-2)` and `y = Y Z^(p-2)`, each left Montgomery's form by a
   multiplication by 1;
3. the flag, `d` in `[1, n-1]` and `Z ≠ 0`, as a mask, selects `04 ‖ x ‖ y`
   or zeros for `out` (big-endian, through `ebx`), and is returned as 0 or 1.

`Z = 0` iff `Q = O`, which the flag rejects as the specification does
(it cannot happen for `d` in `[1, n-1]`, as `G` has the prime order `n`).
Everything is computed whatever the flag, and only the pointers may affect
timing.
-/

namespace VG.Impl.EcKey.X86

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86

/-! Slots of the signature's layout that the public key does not otherwise use. -/

/-- `Y Z^(p-2)`, in Montgomery form. -/
def YM : Nat := RM
/-- `y`. -/
def Y : Nat := SS

/-- The public key's arguments: `(out, d, scratch)`, with `k` and the hash
both `d`. -/
abbrev Args.publicKey : Args := ⟨2, 1, 1, 1⟩

namespace Cfg

variable (c : Impl.Ecdsa.X86.Cfg)

/-- The signature's code up to `Z^(p-2)`, with the public key's arguments. -/
def upToPow : Prog isa :=
  .seq (.block (c.setupWith Args.publicKey)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (ladder c.ladderCfg c.wk) <|
  .seq (pow c.powP c.wk) (.block [])

/-- `04 ‖ x ‖ y` (or zeros) to `out` (through `ebx`), the flag's low bit to
`eax`, and the callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (sc (c.sl FLAG))), .mov .ebx (.mem (Cfg.argOp 0)), .mov .eax (.imm 4),
    .alu .and .eax (.reg .ecx), .store8 (at_ .ebx 0) .al] ++
  storeBE c.n .ebx 1 (c.sl X) ++ storeBE c.n .ebx (1 + 8 * c.n) (c.sl Y) ++
  [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] ++ Impl.Ecdsa.X86.Cfg.restore

/-- `x = X Z⁻¹` and `y = Y Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery
form, the checks of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [Mont.X86.mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86.mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.X86.mul c.MP' c.wk (c.sl YM) (c.sl RY) (c.sl ACC),
    Mont.X86.mul c.MP' c.wk (c.sl Y) (c.sl YM) (c.sl ONE),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-- `vg_ec_<curve>_public_key`. -/
def publicKey : Prog isa := .seq (upToPow c) (middle c)

end Cfg

end VG.Impl.EcKey.X86
