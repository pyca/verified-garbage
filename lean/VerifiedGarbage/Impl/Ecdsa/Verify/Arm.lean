import VerifiedGarbage.Impl.Ecdh.Arm

/-!
# ECDSA signature verification on 32-bit ARM

`vg_ecdsa_<curve>_verify(public, digest, sig, scratch) -> r0` (AAPCS: the
arguments in `r0`–`r3`), for a curve of `n` 64-bit words, from the code of
ECDSA's signature (`Impl/Ecdsa/Arm.lean`) and of ECDH
(`Impl/Ecdh/Arm.lean`), whose layout of the working space it uses, as on
x86 (`Impl/Ecdsa/Verify/X86.lean`):

1. the signature's setup and tables of bits, with the setup reading the
   working space from `scratch` (`r3`), `k` from `sig` (so `r` is read into
   the slot of `k`) and `d` and the hash from `digest` (`Args.verify`), `d`
   shifted right by the bits of the digest that are not `e`'s; then
   `s`, from `sig + len` through `r6`, into `PT` (which only the powers
   use);
2. ECDH's checks of the key (`peerAt .r0`, `validate`): its `x` into the
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

The setup and the tables leave `r0`–`r3`, so `sig` and `public` are read
through `r2` and `r0` after them. Everything is computed whatever the flag,
and only the pointers affect timing, although the contract would let every
input affect it.
-/

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm

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
the signature's `r` (at `sig`), `d` and the hash both `digest` (the key's
`x` is read into the hash's slot after the setup), `scratch` in `r3`, and
the hash in `D` shifted. -/
abbrev Args.verify : Args := ⟨.r2, .r1, .r1, some .r3, some D⟩

namespace Cfg

variable (c : Impl.Ecdsa.Arm.Cfg)

/-- The signature's setup, with verification's arguments, and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block (c.setupWith Args.verify)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- `s`, from `sig + len` through `r6`, into `PT`. -/
def loadS : List Instr :=
  .dp .add .r6 .r2 (.imm (BitVec.ofNat 32 c.C.len)) :: loadBytes c.C.len c.n (c.sl PT) .r6

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
    (Mont.mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N))

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  progs [Mont.mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N),
    Mont.mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N),
    Mont.mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC),
    Mont.mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC),
    Mont.mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE),
    Mont.mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy (2 * c.n) (c.sl UX) (c.sl RX) ++ copy (2 * c.n) (c.sl UY) (c.sl RY) ++
  copy (2 * c.n) (c.sl UZ) (c.sl RZ) ++
  setConst c.n (c.sl RX) 0 ++ setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy (2 * c.n) (c.sl RX) (c.sl DX) ++ copy (2 * c.n) (c.sl RY) (c.sl DY) ++
      copy (2 * c.n) (c.sl RZ) (c.sl DZ)))

/-- The flag's low bit to `r0`, and the callee-saved registers restored. -/
def finish : List Instr :=
  ([.ldr .r10 wb (c.sl FLAG), .dp .and .r0 .r10 (.imm 1)] : List Instr) ++ Impl.Ecdsa.Arm.Cfg.restore

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.mulCall c.SN (c.sl XN) (c.sl X) (c.sl R2N),
    Mont.subCall c.SN (c.sl W) (c.sl XN) (c.sl RM'),
    .block (c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.Arm.Cfg.checkZero c (c.sl W) ++ finish c)]

/-- `[u]G + [v]Q`, into `R`, from the tables of bits of `u` and `v`. -/
def points : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (Point.ladderP c.ladderCfg c.SP) <|
  .seq (.block (save c)) <| .seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (Point.ladderP (Impl.Ecdh.Arm.Cfg.ladderQ c) c.SP) (sum c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq (pow c.powN c.SN) <| .seq (uv c) <| .seq (points c) <|
  .seq (pow c.powP c.SP) (final c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (prefix' c) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.Arm.Cfg.peerAt c .r0)) <| .seq (Impl.Ecdh.Arm.Cfg.validate c) (back c)

end Cfg

end VG.Impl.Ecdsa.Verify.Arm
