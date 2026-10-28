module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE

/-!
# ECDSA signature verification on PPC64LE

`vg_ecdsa_<curve>_verify(public, digest, sig, scratch) -> r3` (ELFv2: the
arguments in `r3`–`r6`), for a curve of `n` 64-bit words, from the code of
ECDSA's signature (`Impl/Ecdsa/PPC64LE.lean`) and of ECDH
(`Impl/Ecdh/PPC64LE.lean`), whose layout of the working space it uses, as on
32-bit ARM (`Impl/Ecdsa/Verify/Arm.lean`):

1. the signature's setup and tables of bits, with the setup reading the
   working space from `scratch` (`r6`), `k` from `sig` (so `r` is read into
   the slot of `k`) and `d` and the hash from `digest` (`Args.verify`), `d`
   shifted right by the bits of the digest that are not `e`'s, keeping
   `public` in `r14` (where the signature keeps `out`) and `sig` in `r12`;
   then `s`, from `sig + len` through `r6`, into `PT` (which only the
   powers use);
2. ECDH's checks of the key (`peerAt .r14`, `validate`): its `x` into the
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

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass
open VG.Impl.Ecdsa.PPC64LE

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
`x` is read into the hash's slot after the setup), `scratch` in `r6`, and
the hash in `D` shifted. -/
abbrev Args.verify : Args := ⟨.r5, .r4, .r4, .r6, some D⟩

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The signature's setup, with verification's arguments, keeping `sig` in
`r12`, and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block (c.setupWith Args.verify ++ [mov .r12 .r5])) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- `s`, from `sig + len` through `r6`, into `PT`. -/
def loadS : List Instr :=
  .addi .r6 .r12 c.C.len :: loadBytes c.C.len c.n (c.sl PT) .r6

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
    (mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N))

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  progs [mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N),
    mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N),
    mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC),
    mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC),
    mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE),
    mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy c.n (c.sl UX) (c.sl RX) ++ copy c.n (c.sl UY) (c.sl RY) ++ copy c.n (c.sl UZ) (c.sl RZ) ++
  VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RX) 0 ++ VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RY) (c.mont 1) ++
  VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++ copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ)))

/-- The flag's low bit to `r3`, and the callee-saved registers restored. -/
def finish : List Instr :=
  ([.load .d .r10 wb (c.sl FLAG), .li .r4 1, .logic .and .r4 .r10 .r4] : List Instr) ++
    Impl.Ecdsa.PPC64LE.Cfg.restore ++ [mov .r3 .r4]

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  progs [mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    mulCall c.SN (c.sl XN) (c.sl X) (c.sl R2N),
    subCall c.SN (c.sl W) (c.sl XN) (c.sl RM'),
    .block (c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W) ++ finish c)]

/-- The scalar at slot `i` to where the multiplications read it: `K`'s slot,
for `vg_<curve>_mul` (`Cfg.mul`; `r`, there, is not read again), else the
table of its bits. -/
def scalarAt (i : Nat) : Prog isa :=
  match c.mul with
  | some _ => .block (copy c.n (c.sl K) (c.sl i))
  | none => bits (c.sl i) (bitsAt c.n 0) (8 * c.n)

/-- `[u]G + [v]Q`, into `R`. -/
def points : Prog isa :=
  .seq (scalarAt c U) <| .seq c.gen <|
  .seq (.block (save c)) <| .seq (scalarAt c V) <|
  .seq (c.qMul Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY) (sum c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq (pow c.powN c.SN) <| .seq (uv c) <| .seq (points c) <|
  .seq (pow c.powP c.SP) (final c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (prefix' c) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r14)) <| .seq (Impl.Ecdh.PPC64LE.Cfg.validate c) (back c)

end Cfg

end VG.Impl.Ecdsa.Verify.PPC64LE
