module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
public import VerifiedGarbage.Spec.Weierstrass

/-! # Coordinate recovery using the existing Montgomery field operations

The exponent, curve coefficients and P-224 nonresidue are materialized in
Lean. The shared ECDSA layout supplies the modulus, Montgomery constants,
field-operation variants and register saves. The only input is a public
compressed encoding; the output is checked before its validity mask is
applied to every byte.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (R2P BP QXM QYM QY W0 W1 W2 W3)

/-- P-224's odd part of `p - 1`. Only that curve uses the descent. -/
def rootQ (c : Cfg) : Nat := (c.C.p - 1) / 2 ^ 96

/-- The extra constants, and the two possible compressed tags. -/
def decompressTag (c : Cfg) : List Instr :=
  [.movzx8 .rdx { base := .r9 }, .store (sc (c.sl D)) .rdx,
    .alu .and .rdx (.imm (-2)), .alu .xor .rdx (.imm 2),
    .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)]

def decompressPeer (c : Cfg) : List Instr :=
  (Ecdh.X86_64.Cfg.consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  decompressTag c ++ c.andFlag ++
  Ecdh.X86_64.Cfg.checkLtP c (c.sl E)

/-- `x R` and `(x³ + a x + b) R`. -/
def rhsOps (c : Cfg) : List FOp :=
  [.mul (c.sl QXM) (c.sl E) (c.sl R2P),
    .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM),
    .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1),
    .add (c.sl W2) (c.sl W3) (c.sl BP)]

/-- The second table stays separate from the nine-word multiplication's
temporary area, which occupies part of the first table. -/
def rootPow (c : Cfg) (acc table : Nat) : PowCfg :=
  { M := c.MP', acc := c.sl acc, tmp := c.sl PT, base := c.sl W2,
    one := c.sl ONEP, bits := bitsAt c.n table, nbits := 64 * c.n }

def squareStep (c : Cfg) (slot : Nat) : Prog isa :=
  .block (opCode c.MP' (.mul (c.sl slot) (c.sl slot) (c.sl slot)) ++
    [.alu .sub .rbx (.imm 1), .alu .test .rbx (.reg .rbx)])

/-- Square `T3` `rbx` times, with zero iterations allowed. -/
def squarePower (c : Cfg) : Prog isa :=
  .seq (.block [.alu .test .rbx (.reg .rbx)])
    (.ite .e (.block []) (.loop (squareStep c T3) .ne))

/-- The power tested in one P-224 descent round. -/
def descentPower (c : Cfg) : Prog isa :=
  .seq (.block (copy c.n (c.sl T3) (c.sl T0) ++
    [.mov .rbx (.mem (sc (c.sl T2))), .alu .sub .rbx (.imm 1)])) (squarePower c)

def descentChoose (c : Cfg) : List Instr :=
  opCode c.MP' (.sub (c.sl W0) (c.sl T3) (c.sl ONEP)) ++
    Ecdh.X86_64.Cfg.zero c (c.sl W0) ++ [.mov .rcx (.reg .rdx)] ++
    sel c.n (c.sl T4) (c.sl T1) (c.sl ONEP)

def descentOps (c : Cfg) : List FOp :=
  [.mul (c.sl ACC) (c.sl ACC) (c.sl T4),
    .mul (c.sl T4) (c.sl T4) (c.sl T4),
    .mul (c.sl T0) (c.sl T0) (c.sl T4),
    .mul (c.sl T1) (c.sl T1) (c.sl T1)]

def descentCounter (c : Cfg) : List Instr :=
  [.mov .rbx (.mem (sc (c.sl T2))), .alu .sub .rbx (.imm 1),
    .store (sc (c.sl T2)) .rbx, .alu .test .rbx (.reg .rbx)]

/-- One round of the P-224 descent: `r` in `ACC`, `t` in `T0`, `c` in
`T1`, rounds remaining at `T2`, the tested power in `T3`, and `b` in `T4`. -/
def descentRound (c : Cfg) : Prog isa :=
  progs [descentPower c, .block (descentChoose c), fprogB c.MP' (descentOps c),
    .block (descentCounter c)]

/-- Materialize a public exponent and use the existing verified power loop. -/
def rootPower (c : Cfg) (e table : Nat) : Prog isa :=
  progs [.block (setConst c.n (c.sl EXPP) e),
    bits (c.sl EXPP) (bitsAt c.n table) (8 * c.n), pow (rootPow c ACC table)]

def tonelliPowers (c : Cfg) : Prog isa :=
  progs [rootPower c ((rootQ c + 1) / 2) 1,
    .block (copy c.n (c.sl T5) (c.sl ACC)), rootPower c (rootQ c) 2]

def tonelliSetup (c : Cfg) : List Instr :=
  let zq := (Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)).val
  copy c.n (c.sl T0) (c.sl ACC) ++ copy c.n (c.sl ACC) (c.sl T5) ++
    setConst c.n (c.sl T1) (c.mont zq) ++ setConst 1 (c.sl T2) 95

def rootCandidate (c : Cfg) : Prog isa :=
  if c.C.p % 4 = 3 then rootPower c ((c.C.p + 1) / 4) 2
  else
    progs [tonelliPowers c, .block (tonelliSetup c), .loop (descentRound c) .ne]

/-- The mismatch mask between the recovered canonical `y` and the tag. -/
def parityMask (c : Cfg) : List Instr :=
  [.mov .rdx (.mem (sc (c.sl QY))), .alu .xor .rdx (.mem (sc (c.sl D))),
    .alu .and .rdx (.imm 1), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

def selectRoot (c : Cfg) : Prog isa :=
  progs [opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE)),
    .block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0))]

def checkRootOps (c : Cfg) : List FOp :=
  [.mul (c.sl QYM) (c.sl QY) (c.sl R2P),
    .mul (c.sl W1) (c.sl QYM) (c.sl QYM),
    .sub (c.sl W3) (c.sl W1) (c.sl W2)]

def checkRootChecks (c : Cfg) : List Instr :=
  Ecdh.X86_64.Cfg.checkZero c (c.sl W3) ++ (parityMask c ++
    ([.mov .rdx (.reg .rcx), .alu .xor .rdx (.imm (-1))] ++ c.andFlag))

/-- Check the chosen root's square and parity, including the odd-zero
case, before any output is accepted. -/
def checkRoot (c : Cfg) : Prog isa :=
  .seq (fprogB c.MP' (checkRootOps c)) (.block (checkRootChecks c))

def decompressFinish (c : Cfg) : List Instr :=
  [.mov .rcx (.mem (sc (c.sl FLAG))), .mov32 .rax (.imm 4),
    .alu .and .rax (.reg .rcx), .store8 { base := .rsi } .rax] ++
  storeBytes c.C.len c.n .rsi 1 (c.sl E) ++
  storeBytes c.C.len c.n .rsi (1 + c.C.len) (c.sl QY) ++
  [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] ++
  Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- Recover and validate the coordinate before writing any output. -/
def recoverCoordinate (c : Cfg) : Prog isa :=
  .seq (rootCandidate c) (.seq (selectRoot c) (checkRoot c))

def decompress (c : Cfg) : Prog isa :=
  progs [.block args, .block (c.setupWith none), .block (decompressPeer c),
    fprogB c.MP' (rhsOps c), recoverCoordinate c,
    .block (decompressFinish c)]

end VG.Impl.EcKey.Compressed.X86_64
