import VerifiedGarbage.Impl.Ecdh.X86

/-!
# ECDSA signature verification on x86 (32-bit)

`vg_ecdsa_<curve>_verify(public, digest, sig, scratch) -> eax` (cdecl: the
arguments at `[esp + 4]` to `[esp + 16]`), for a curve of `n` 64-bit words,
from the code of ECDSA's signature (`Impl/Ecdsa/X86.lean`) and of ECDH
(`Impl/Ecdh/X86.lean`), whose layout of the working space it uses, as on
x86-64 and AArch64 (`Impl/Ecdsa/Verify/AArch64.lean`):

1. the signature's setup and tables of bits, with the setup reading the
   working space from `scratch`, `k` from `sig` (so `r` is read into the
   slot of `k`) and `d` and the hash from `digest` (`Args.verify`), `d`
   shifted right by the bits of the digest that are not `e`'s; then
   `s`, from `sig + len` through `ebx`, into `PT` (which only the powers
   use);
2. ECDH's checks of the key (`peerAt 0`, `validate`): its `x` into the
   hash's slot, its first byte, `x < p`, `y < p` and the curve's equation,
   into the flag, and the key's point, or `G` if the flag is clear, to the
   slots of ECDH's ladder;
3. the masks of `r` and `s` in `[1, n-1]` into the flag, and
   `w = s^(n-2)`, in Montgomery form modulo `n`;
4. `u = e w` and `v = r w` modulo `n`, out of Montgomery's form;
5. `[u]G` by the signature's ladder (from the table of `u`'s bits), saved
   to `U`, and `R` reset to `O`; then `[v]Q` by ECDH's ladder (from the
   table of `v`'s bits) and `[u]G + [v]Q` by the complete addition, into
   `R`;
6. `Z^(p-2)` by the signature's power, `x = X Z^(p-2)` out of Montgomery's
   form, and the masks of `Z ≠ 0` and `x R ≡ r R` modulo `n` into the
   flag, which is returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers affect
timing, although the contract would let every input affect it.
-/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86

/-! Slots of the signature's layout, as verification uses them, after ECDH's
checks of the key: `K` holds `r`, `D` the hash and `PT` `s` (until the
power modulo `n`). -/

/-- `s R mod n`, the power's base. -/
def SM' : Nat := KM
/-- `e R mod n` and `r R mod n`. -/
def EM' : Nat := EM
def RM' : Nat := DM
/-- `u R` and `v R` modulo `n`, then `u` and `v`. -/
def UM : Nat := TT
def VM : Nat := SM
def U : Nat := XM
def V : Nat := X
/-- `[u]G`. -/
def UX : Nat := TT
def UY : Nat := SM
def UZ : Nat := KM
/-- `x R mod n`, and `x R - r R mod n`. -/
def XN : Nat := RM
def W : Nat := EM

/-- Verification's arguments: `(public, digest, sig, scratch)`, with `k`
the signature's `r` (at `sig`), and `d` and the hash both `digest` (the
key's `x` is read into the hash's slot after the setup), shifting the hash
in `D`. -/
abbrev Args.verify : Args := ⟨3, 2, 1, 1, some D⟩

namespace Cfg

variable (c : Impl.Ecdsa.X86.Cfg)

/-- The signature's setup, with verification's arguments, and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block (c.setupWith Args.verify)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- `s`, from `sig + len` through `ebx`, into `PT`. -/
def loadS : List Instr :=
  [.mov .ebx (.mem (Cfg.argOp 2)), .alu .add .ebx (.imm (BitVec.ofNat 32 c.C.len))] ++
  loadBytes c.C.len c.n (c.sl PT) .ebx

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
    (Mont.X86.mul c.MN' c.wk (c.sl SM') (c.sl PT) (c.sl R2N))

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  progs [Mont.X86.mul c.MN' c.wk (c.sl EM') (c.sl D) (c.sl R2N),
    Mont.X86.mul c.MN' c.wk (c.sl RM') (c.sl K) (c.sl R2N),
    Mont.X86.mul c.MN' c.wk (c.sl UM) (c.sl EM') (c.sl ACC),
    Mont.X86.mul c.MN' c.wk (c.sl VM) (c.sl RM') (c.sl ACC),
    Mont.X86.mul c.MN' c.wk (c.sl U) (c.sl UM) (c.sl ONE),
    Mont.X86.mul c.MN' c.wk (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy (2 * c.n) (c.sl UX) (c.sl RX) ++ copy (2 * c.n) (c.sl UY) (c.sl RY) ++
  copy (2 * c.n) (c.sl UZ) (c.sl RZ) ++
  setConst c.n (c.sl RX) 0 ++ setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprog c.MP' c.wk (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy (2 * c.n) (c.sl RX) (c.sl DX) ++ copy (2 * c.n) (c.sl RY) (c.sl DY) ++
      copy (2 * c.n) (c.sl RZ) (c.sl DZ)))

/-- The flag's low bit to `eax`, and the callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (sc (c.sl FLAG))), .mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] ++
    Impl.Ecdsa.X86.Cfg.restore

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  progs [Mont.X86.mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86.mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.X86.mul c.MN' c.wk (c.sl XN) (c.sl X) (c.sl R2N),
    .block (Mont.X86.sub c.MN' c.wk (c.sl W) (c.sl XN) (c.sl RM')),
    .block (c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.X86.Cfg.checkZero c (c.sl W) ++ finish c)]

/-- `[u]G + [v]Q`, into `R`, from the tables of bits of `u` and `v`. -/
def points : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (ladder c.ladderCfg c.wk) <|
  .seq (.block (save c)) <| .seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (ladder (Impl.Ecdh.X86.Cfg.ladderQ c) c.wk) (sum c)

/-- Fixed-base comb for `[u]G`, followed by the existing variable-base ladder. -/
def pointsComb : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq c.gMul <|
  .seq (.block (save c)) <| .seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (ladder (Impl.Ecdh.X86.Cfg.ladderQ c) c.wk) (sum c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq (pow c.powN c.wk) <| .seq (uv c) <| .seq (points c) <|
  .seq (pow c.powP c.wk) (final c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (prefix' c) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 0)) <| .seq (Impl.Ecdh.X86.Cfg.validate c) (back c)

/-- Verification body using the comb for its fixed-base multiplication. -/
def verifyCombBody : Prog isa :=
  .seq (prefix' c) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 0)) <| .seq (Impl.Ecdh.X86.Cfg.validate c) <|
  .seq (scalars c) <| .seq (pow c.powN c.wk) <| .seq (uv c) <| .seq (pointsComb c) <|
  .seq (pow c.powP c.wk) (final c)

/-- Acquire the static table before loading the cdecl arguments. -/
def verifyComb : Prog isa := .seq c.tableAddr (verifyCombBody c)

end Cfg

end VG.Impl.Ecdsa.Verify.X86
