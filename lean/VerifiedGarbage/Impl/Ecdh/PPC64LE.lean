module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-!
# ECDH on PPC64LE

`vg_ecdh_<curve>(out, d, peer, scratch) -> r3` (ELFv2: the arguments in
`r3`–`r6`), for a curve of `n` 64-bit words, from the code of ECDSA's
signature (`Impl/Ecdsa/PPC64LE.lean`), whose layout of the working space it
uses, as on 32-bit ARM (`Impl/Ecdh/Arm.lean`):

1. the signature's setup, reading the working space from `scratch` (`r6`)
   and `k`, `d` and the hash all from `d` (`Args.ecdh`), and `peer` (`r5`)
   to `r12`, which the setup and the tables keep;
2. the signature's tables of bits;
3. `R² mod p` and `b R mod p` to slots of their own, the peer's `x` (at
   `peer + 1`) to the hash's slot and its `y` to another, and into the flag
   the masks of the peer's first byte being `04`, `x < p` and `y < p`;
4. `x` and `y` into Montgomery's form, and the mask of `y² = x³ + a x + b`
   into the flag;
5. the peer's point, or `G` if the flag is clear (so the ladder always runs
   on a point of the curve), to the slots the ladder takes its point from;
6. `[d]P` by the signature's ladder, and `Z^(p-2)` by its power;
7. `x = X Z^(p-2)`, out of Montgomery's form, and the masks of `d` in
   `[1, n-1]` and `Z ≠ 0` into the flag, which selects `x` or zeros for
   `out` (big-endian, through `r14`, where the setup keeps it) and is
   returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers may affect
timing (the contract would let the peer's public key affect it too).
-/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass
open VG.Impl.Ecdsa.PPC64LE

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
/-- The point the ladder multiplies: the peer's, or `G`. -/
def PX : Nat := RM
def PY : Nat := SS

/-- ECDH's arguments: `(out, d, peer, scratch)`, with `k` and the hash both
`d` (the peer's `x` is read into the hash's slot after the setup), and
`scratch` in `r6`. -/
abbrev Args.ecdh : Args := ⟨.r4, .r4, .r4, .r6, none⟩

namespace Cfg

variable (c : Impl.Ecdsa.PPC64LE.Cfg)

/-- The constants ECDH adds to the signature's. -/
def consts : List (Nat × Nat) := [(R2P, c.R * c.R % c.C.p), (BP, c.mont c.C.b)]

/-- `[a] < p`: the flag `&=` its mask. -/
def checkLtP (a : Nat) : List Instr := c.ltM (c.sl MP) a ++ c.andFlag

/-- `[a] = 0`: the flag `&=` its mask, `-(-m) - 1` of `nonzero`'s mask `m`
(through `r4`). -/
def checkZero (a : Nat) : List Instr :=
  c.nonzero a ++ ([.li .r4 0, .sub .r5 .r4 .r5, .subi .r5 .r5 1] : List Instr) ++ c.andFlag

/-- The first byte of the key `q` points to is `04`: the flag `&=` its mask,
through `r4`, `r5` and `r7` (all ones iff `byte ^ 4 = 0`, the top bit of
`(byte ^ 4) - 1`, negated). -/
def checkLead (q : Reg) : List Instr :=
  ([.lbz .r4 q 0, .li .r7 4, .logic .xor .r4 .r4 .r7, .subi .r4 .r4 1, .lsr .d .r4 .r4 63,
    .li .r5 0, .sub .r5 .r5 .r4] : List Instr) ++ c.andFlag

/-- The constants, the `x` and `y` of the key `q` points to (through `r6`,
from its byte 1), and the checks of its first byte, `x` and `y`. -/
def peerAt (q : Reg) : List Instr :=
  (consts c).flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
  ([.addi .r6 q 1] : List Instr) ++ loadBytes c.C.len c.n (c.sl E) .r6 ++
  ([.addi .r6 .r6 c.C.len] : List Instr) ++ loadBytes c.C.len c.n (c.sl QY) .r6 ++
  checkLead c q ++ checkLtP c (c.sl E) ++ checkLtP c (c.sl QY)

/-- The setup, keeping the peer's key's pointer (`r5`) in `r12`, which the
setup and the tables of bits keep. -/
def setup : List Instr := c.setupWith Args.ecdh ++ [mov .r12 .r5]

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl QYM) (c.sl QYM), .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM), .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl W3) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- The point to the ladder's slots: the peer's if the flag is set, else
`G` (the flag is the mask `r10`). -/
def select : List Instr :=
  ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++
  sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)

/-- `x` and `y` into Montgomery's form, the check that the point is on the
curve, and the point the ladder multiplies. -/
def validate : Prog isa :=
  .seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P)) <|
  .seq (mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P)) <|
  .seq (fprog c.SP (curveOps c)) (.block (checkZero c (c.sl W1) ++ select c))

/-- The ladder of the signature, from the point at `PX`, `PY`, `ONEP`. -/
def ladderQ : LadderCfg := { c.ladderCfg with G := c.pt PX PY ONEP }

/-- `x` (or zeros) to `out` (in `r14`), the flag's low bit to `r3`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++ storeBytes c.C.len c.n .r14 0 (c.sl X) ++
  ([.li .r4 1, .logic .and .r4 .r10 .r4] : List Instr) ++ Impl.Ecdsa.PPC64LE.Cfg.restore ++ [mov .r3 .r4]

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, the checks
of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-- `vg_ecdh_<curve>`. -/
def exchange : Prog isa :=
  .seq (.block (setup c)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (.block (peerAt c .r12)) <|
  .seq (validate c) <|
  .seq (c.qMul PX PY) <| .seq (pow c.powP c.SP) (middle c)

end Cfg

end VG.Impl.Ecdh.PPC64LE
