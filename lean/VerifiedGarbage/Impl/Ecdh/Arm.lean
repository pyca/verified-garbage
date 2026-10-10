import VerifiedGarbage.Impl.Ecdsa.Arm

/-!
# ECDH on 32-bit ARM

`vg_ecdh_<curve>(out, d, peer, scratch) -> r0` (AAPCS: the arguments in
`r0`–`r3`), for a curve of `n` 64-bit words, from the code of ECDSA's
signature (`Impl/Ecdsa/Arm.lean`), whose layout of the working space it
uses, as on x86 (`Impl/Ecdh/X86.lean`):

1. the signature's setup and tables of bits, with the setup reading the
   working space from `scratch` (`r3`) and `k`, `d` and the hash all from
   `d` (`Args.ecdh`); neither changes `peer` (`r2`);
2. `R² mod p` and `b R mod p` to slots of their own, the peer's `x` (at
   `peer + 1`) to the hash's slot and its `y` to another, and into the flag
   the masks of the peer's first byte being `04`, `x < p` and `y < p`;
3. `x` and `y` into Montgomery's form, and the mask of `y² = x³ + a x + b`
   into the flag;
4. the peer's point, or `G` if the flag is clear (so the ladder always runs
   on a point of the curve), to the slots the ladder takes its point from;
5. `[d]P` by the signature's ladder, and `Z^(p-2)` by its power;
6. `x = X Z^(p-2)`, out of Montgomery's form, and the masks of `d` in
   `[1, n-1]` and `Z ≠ 0` into the flag, which selects `x` or zeros for
   `out` (big-endian, through `lr`, where the setup keeps it) and is
   returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers may affect
timing (the contract would let the peer's public key affect it too).
-/

namespace VG.Impl.Ecdh.Arm

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm

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
`scratch` in `r3`. -/
abbrev Args.ecdh : Args := ⟨.r1, .r1, .r1, some .r3, none⟩

namespace Cfg

variable (c : Impl.Ecdsa.Arm.Cfg)

/-- The signature's setup, with ECDH's arguments, and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block (c.setupWith Args.ecdh)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- The constants ECDH adds to the signature's. -/
def consts : List (Nat × Nat) := [(R2P, c.R * c.R % c.C.p), (BP, c.mont c.C.b)]

/-- `[a] < p`: the flag `&=` its mask. -/
def checkLtP (a : Nat) : List Instr := c.ltM (c.sl MP) a ++ c.andFlag

/-- `[a] = 0`: the flag `&=` its mask, `-(-m) - 1` of `nonzero`'s mask `m`
(through `r4`). -/
def checkZero (a : Nat) : List Instr :=
  c.nonzero a ++ ([.mov .r4 (.imm 0), .dp .sub .r5 .r4 (.reg .r5), .dp .sub .r5 .r5 (.imm 1)] : List Instr) ++ c.andFlag

/-- The first byte of the key `q` points to is `04`: the flag `&=` its mask,
through `r4` and `r5` (all ones iff `byte ^ 4 = 0`, the top bit of
`(byte ^ 4) - 1`, negated). -/
def checkLead (q : Reg) : List Instr :=
  ([.ldrb .r4 q 0, .dp .eor .r4 .r4 (.imm 4), .dp .sub .r4 .r4 (.imm 1), .mov .r4 (.shifted .r4 .lsr 31),
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4)] : List Instr) ++ c.andFlag

/-- The constants, the `x` and `y` of the key `q` points to (through `r6`,
from its byte 1), and the checks of its first byte, `x` and `y` (also
signature verification's, with its key). -/
def peerAt (q : Reg) : List Instr :=
  (consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  ([.dp .add .r6 q (.imm 1)] : List Instr) ++ loadBytes c.C.len c.n (c.sl E) .r6 ++
  ([.dp .add .r6 .r6 (.imm (BitVec.ofNat 32 c.C.len))] : List Instr) ++ loadBytes c.C.len c.n (c.sl QY) .r6 ++
  checkLead c q ++ checkLtP c (c.sl E) ++ checkLtP c (c.sl QY)

/-- The peer's key: `peerAt` its argument, `r2`. -/
def peer : List Instr := peerAt c .r2

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl QYM) (c.sl QYM), .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM), .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl W3) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- The point to the ladder's slots: the peer's if the flag is set, else
`G` (the flag is the mask `r10`). -/
def select : List Instr :=
  ([.ldr .r10 wb (c.sl FLAG)] : List Instr) ++
  sel (2 * c.n) (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel (2 * c.n) (c.sl PY) (c.sl GY) (c.sl QYM)

/-- `x` and `y` into Montgomery's form, the check that the point is on the
curve, and the point the ladder multiplies. -/
def validate : Prog isa :=
  .seq (Mont.mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P)) <|
  .seq (Mont.mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P)) <|
  .seq (fprog c.SP (curveOps c)) (.block (checkZero c (c.sl W1) ++ select c))

/-- The ladder of the signature, from the point at `PX`, `PY`, `ONEP`. -/
def ladderQ : LadderCfg := { c.ladderCfg with G := c.pt PX PY ONEP }

/-- `x` (or zeros) to `out` (in `lr`), the flag's low bit to `r0`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  ([.ldr .r10 wb (c.sl FLAG)] : List Instr) ++ storeBytes c.C.len c.n .lr 0 (c.sl X) ++
  ([.dp .and .r0 .r10 (.imm 1)] : List Instr) ++ Impl.Ecdsa.Arm.Cfg.restore

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, the checks
of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-- `vg_ecdh_<curve>`. -/
def exchange : Prog isa :=
  .seq (prefix' c) <| .seq (.block (peer c)) <| .seq (validate c) <|
  .seq (ladder (ladderQ c) c.SP) <| .seq (pow c.powP c.SP) (middle c)

end Cfg

end VG.Impl.Ecdh.Arm
