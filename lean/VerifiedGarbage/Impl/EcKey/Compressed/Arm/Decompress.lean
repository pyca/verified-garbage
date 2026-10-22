module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Spec.Weierstrass

/-! # Shared SEC 1 coordinate recovery on ARMv7 -/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (R2P BP QXM QYM QY W0 W1 W2 W3)

def rootQ (c : Cfg) : Nat := (c.C.p - 1) / 2 ^ 96

def decompressTag (c : Cfg) : List Instr :=
  [.ldrb .r4 .r1 0, .str .r4 wb (c.sl D), .dp .orr .r4 .r4 (.imm 1),
    .dp .eor .r4 .r4 (.imm 3), .dp .sub .r4 .r4 (.imm 1),
    .mov .r4 (.shifted .r4 .lsr 31), .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r4)]

def decompressPeer (c : Cfg) : List Instr :=
  (Ecdh.Arm.Cfg.consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.dp .add .r6 .r1 (.imm 1)] ++ loadBytes c.C.len c.n (c.sl E) .r6 ++
  decompressTag c ++ c.andFlag ++ Ecdh.Arm.Cfg.checkLtP c (c.sl E)

def rhsOps (c : Cfg) : List FOp :=
  [.mul (c.sl QXM) (c.sl E) (c.sl R2P),
    .mul (c.sl W1) (c.sl QXM) (c.sl QXM), .mul (c.sl W2) (c.sl W1) (c.sl QXM),
    .mul (c.sl W1) (c.sl AP) (c.sl QXM), .add (c.sl W3) (c.sl W2) (c.sl W1),
    .add (c.sl W2) (c.sl W3) (c.sl BP)]

def rootPow (c : Cfg) (table : Nat) : PowCfg :=
  ⟨c.MP', c.sl ACC, c.sl PT, c.sl W2, c.sl ONEP, bitsAt c.n table, 64 * c.n⟩

def rootPower (c : Cfg) (e table : Nat) : Prog isa :=
  progs [.block (setConst c.n (c.sl EXPP) e),
    bits (c.sl EXPP) (bitsAt c.n table) (8 * c.n), pow (rootPow c table) c.SP]

def squareStep (c : Cfg) : Prog isa :=
  .seq (Mont.mulCall c.SP (c.sl T3) (c.sl T3) (c.sl T3)) (.block [decCounter, testCounter])

def squarePower (c : Cfg) : Prog isa :=
  .seq (.block [testCounter]) (.ite .eq (.block []) (.loop (squareStep c) .ne))

def descentPower (c : Cfg) : Prog isa :=
  .seq (.block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++
    [.ldr .r11 wb (c.sl T2), decCounter])) (squarePower c)

def zeroMask (c : Cfg) (a : Nat) : List Instr :=
  c.nonzero a ++ [.mov .r4 (.imm 0), .dp .sub .r5 .r4 (.reg .r5), .dp .sub .r5 .r5 (.imm 1)]

def descentChoose (c : Cfg) : Prog isa :=
  .seq (Mont.subCall c.SP (c.sl W0) (c.sl T3) (c.sl ONEP))
    (.block (zeroMask c (c.sl W0) ++ [.mov .r10 (.reg .r5)] ++
      sel (2 * c.n) (c.sl T4) (c.sl T1) (c.sl ONEP)))

def descentOps (c : Cfg) : List FOp :=
  [.mul (c.sl ACC) (c.sl ACC) (c.sl T4), .mul (c.sl T4) (c.sl T4) (c.sl T4),
    .mul (c.sl T0) (c.sl T0) (c.sl T4), .mul (c.sl T1) (c.sl T1) (c.sl T1)]

def descentCounter (c : Cfg) : List Instr :=
  [.ldr .r11 wb (c.sl T2), decCounter, .str .r11 wb (c.sl T2), testCounter]

def descentRound (c : Cfg) : Prog isa :=
  progs [descentPower c, descentChoose c, fprog c.SP (descentOps c), .block (descentCounter c)]

def tonelliPowers (c : Cfg) : Prog isa :=
  progs [rootPower c ((rootQ c + 1) / 2) 1,
    .block (copy (2 * c.n) (c.sl T5) (c.sl ACC)), rootPower c (rootQ c) 2]

def tonelliSetup (c : Cfg) : List Instr :=
  let zq := (Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)).val
  copy (2 * c.n) (c.sl T0) (c.sl ACC) ++ copy (2 * c.n) (c.sl ACC) (c.sl T5) ++
  setConst c.n (c.sl T1) (c.mont zq) ++ [.mov .r4 (.imm 95), .str .r4 wb (c.sl T2)]

def rootCandidate (c : Cfg) : Prog isa :=
  if c.C.p % 4 = 3 then rootPower c ((c.C.p + 1) / 4) 2
  else progs [tonelliPowers c, .block (tonelliSetup c), .loop (descentRound c) .ne]

def parityMask (c : Cfg) : List Instr :=
  [.ldr .r4 wb (c.sl QY), .ldr .r5 wb (c.sl D), .dp .eor .r5 .r5 (.reg .r4),
    .dp .and .r5 .r5 (.imm 1), .mov .r4 (.imm 0), .dp .sub .r10 .r4 (.reg .r5)]

def selectRoot (c : Cfg) : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE),
    Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY),
    .block (parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))]

def checkRootOps (c : Cfg) : List FOp :=
  [.mul (c.sl QYM) (c.sl QY) (c.sl R2P), .mul (c.sl W1) (c.sl QYM) (c.sl QYM),
    .sub (c.sl W3) (c.sl W1) (c.sl W2)]

def invertMask : List Instr :=
  [.dp .add .r5 .r10 (.imm 1), .mov .r4 (.imm 0), .dp .sub .r5 .r4 (.reg .r5)]

def checkRootChecks (c : Cfg) : List Instr :=
  Ecdh.Arm.Cfg.checkZero c (c.sl W3) ++ (parityMask c ++
    (invertMask ++ c.andFlag))

def checkRoot (c : Cfg) : Prog isa :=
  .seq (fprog c.SP (checkRootOps c)) (.block (checkRootChecks c))

def decompressFinish (c : Cfg) : List Instr :=
  EcKey.Arm.Cfg.finishWith c E QY

def recoverCoordinate (c : Cfg) : Prog isa :=
  .seq (rootCandidate c) (.seq (selectRoot c) (checkRoot c))

def decompress (c : Cfg) : Prog isa :=
  progs [.block (c.setupWith args), .block (decompressPeer c), fprog c.SP (rhsOps c),
    recoverCoordinate c, .block (decompressFinish c)]

end VG.Impl.EcKey.Compressed.Arm
