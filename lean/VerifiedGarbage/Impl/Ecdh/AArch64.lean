import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# ECDH on AArch64

`vg_ecdh_<curve>(out = x0, d = x1, peer = x2, scratch = x3) -> w0`, for a
curve of `n` 64-bit words, from the code of ECDSA's signature
(`Impl/Ecdsa/AArch64.lean`), whose layout of the working space it uses, as
on x86-64 (`Impl/Ecdh/X86_64.lean`):

1. `scratch` to `x4`, `peer` to `x6`, `d`'s pointer to `x3` (the
   signature's `k`) and `peer + 1` to `x2` (its hash); then the
   signature's setup and tables of bits, unchanged: `d` is read into the
   slots of `k` and `d`, the peer's `x` into that of the hash;
2. `R² mod p` and `b R mod p` to slots of their own, the peer's `y` to
   another, and into the flag the masks of the peer's first byte being
   `04`, `x < p` and `y < p`;
3. `x` and `y` into Montgomery's form, and the mask of `y² = x³ + a x + b`
   into the flag;
4. the peer's point, or `G` if the flag is clear (so the window method always runs
   on a point of the curve), to the slots the window method takes its point from;
5. `d + 8 Σ_{j<J} 16^j` and its bits, `[d]P` by the window method (`WinCfg.window`, its
   table of `[1 … 8]P` past the signature's tables of bits), and `Z^(p-2)` by the
   signature's power;
6. `x = X Z^(p-2)`, out of Montgomery's form, and the masks of `d` in
   `[1, n-1]` and `Z ≠ 0` into the flag, which selects `x` or zeros for
   `out` (big-endian) and is returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers may affect
timing (the contract would let the peer's public key affect it too).
-/

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64

/-! Slots of the signature's layout, as ECDH uses them. The hash's slot `E`
holds the peer's `x`. -/

/-- The peer's `y`. -/
def QY : Nat := RR
/-- `R² mod p`. -/
def R2P : Nat := DM
/-- `b R mod p`. -/
def BP : Nat := EM
/-- `x R mod p`. -/
def QXM : Nat := XM
/-- `y R mod p`. -/
def QYM : Nat := X
/-- Temporaries of the check that the peer's point is on the curve. -/
def W0 : Nat := KM
def W1 : Nat := TT
def W2 : Nat := SM
def W3 : Nat := RM
/-- The point the window method multiplies: the peer's, or `G`. -/
def PX : Nat := RM
def PY : Nat := SS

namespace Cfg

variable (c : Impl.Ecdsa.AArch64.Cfg)

/-- `scratch` to `x4`, `peer` to `x6`, `d`'s pointer to `x3` and
`peer + 1` to `x2`: the signature's arguments, with `k` and `d` both `d`
and the hash the peer's `x`. -/
def args : List Instr :=
  [.addImm .x .x4 .x3 0, .addImm .x .x6 .x2 0, .addImm .x .x3 .x1 0, .addImm .x .x2 .x2 1]

/-- The signature's setup and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- The constants ECDH adds to the signature's. -/
def consts : List (Nat × Nat) := [(R2P, c.R * c.R % c.C.p), (BP, c.mont c.C.b)]

/-- The mask `x2` of `[a] < p` (all ones if it is), through `x1`, `x7` and
`x16`. -/
def ltP (a : Nat) : List Instr :=
  zero7 :: ((List.range c.n).flatMap fun j =>
    [ld .x1 (a + 8 * j), ld .x2 (c.sl MP + 8 * j),
      if j = 0 then .subs .x .x16 .x1 .x2 else .sbcs .x .x16 .x1 .x2]) ++
  [.sbc .x .x2 .x7 .x7]

/-- `[a] < p`: the flag `&=` its mask. -/
def checkLtP (a : Nat) : List Instr := ltP c a ++ c.andFlag

/-- The mask `x2` of `x1 = 0` (all ones if it is), with `x7 = 0`, through
`x5` and `x16`. -/
def isZero : List Instr := [.movz .x .x5 1 0, .subs .x .x16 .x1 .x5, .sbc .x .x2 .x7 .x7]

/-- The mask `x2` of `[a] = 0` (all ones if it is), through `x1`, `x5`, `x7`
and `x16`. -/
def zero (a : Nat) : List Instr :=
  [zero7, ld .x1 a] ++ ((List.range (c.n - 1)).flatMap fun j =>
    [ld .x2 (a + 8 * (j + 1)), .logic .orr .x .x1 .x1 .x2]) ++ isZero

/-- `[a] = 0`: the flag `&=` its mask. -/
def checkZero (a : Nat) : List Instr := zero c a ++ c.andFlag

/-- The peer's first byte is `04`: the flag `&=` its mask. -/
def checkLead : List Instr :=
  [zero7, .ldrb .x1 .x6 0, .movz .x .x5 4 0, .logic .eor .x .x1 .x1 .x5] ++ isZero ++ c.andFlag

/-- The constants, the peer's `y`, and the checks of its first byte, `x`
and `y`. -/
def peer : List Instr :=
  (consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.addImm .x .x2 .x6 (1 + 8 * c.n)] ++
  loadBE c.n (c.sl QY) .x2 ++ checkLead c ++ checkLtP c (c.sl E) ++ checkLtP c (c.sl QY)

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl QYM) (c.sl QYM), .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM), .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl W3) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- The point to the window method's slots: the peer's if the flag is set, else
`G`. -/
def select : List Instr :=
  [ld .x3 (c.sl FLAG)] ++
  sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)

/-- `x` and `y` into Montgomery's form, the check that the point is on the
curve, and the point the window method multiplies. -/
def validate : Prog isa :=
  blocks ([Mont.AArch64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P),
    Mont.AArch64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)] ++
    (curveOps c).map (opCode c.MP') ++ [checkZero c (c.sl W1) ++ select c])

/-- `x` (or zeros) to `out`, `x19` and `x20` restored, and the flag's low
bit to `x0`. -/
def finish : List Instr :=
  [ld .x3 (c.sl FLAG)] ++ storeBE c.n .x20 0 (c.sl X) ++
  Impl.Ecdsa.AArch64.Cfg.saved.map (fun (r, d) => ld r d) ++
  [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, the checks
of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  blocks [Mont.AArch64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.AArch64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c]

/-- `vg_ecdh_<curve>`. -/
def exchange : Prog isa :=
  .seq (.block (args)) <| .seq (prefix' c) <| .seq (.block (peer c)) <| .seq (validate c) <|
  .seq (c.winPrep (c.sl K)) <| .seq (WinCfg.window (c.winCfg PX PY)) <| .seq (ChainCfg.pow c.powP) (middle c)

end Cfg

end VG.Impl.Ecdh.AArch64
