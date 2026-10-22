module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Spec.Weierstrass

/-! # Shared SEC 1 coordinate recovery on ARMv7 -/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP QXM QYM QY W0 W1 W2 W3)

def rootQ (c : Cfg) : Nat := (c.C.p - 1) / 2 ^ 96

def decompressTag (c : Cfg) : List Instr :=
  [.mov .ebx (.mem (Cfg.argOp 1)), .movzx8 .edx (at_ .ebx 0), .store (sc (c.sl D)) .edx,
    .alu .or .edx (.imm 1), .alu .xor .edx (.imm 3), .alu .sub .edx (.imm 1),
    .alu .sbb .edx (.reg .edx)]

def decompressPeer (c : Cfg) : List Instr :=
  (Ecdh.X86.Cfg.consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.mov .ebx (.mem (Cfg.argOp 1)), .alu .add .ebx (.imm 1)] ++ loadBytes c.C.len c.n (c.sl E) .ebx ++
  decompressTag c ++ c.andFlag ++ Ecdh.X86.Cfg.checkLtP c (c.sl E)

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
  .seq (.block [testCounter]) (.ite .e (.block []) (.loop (squareStep c) .ne))

def descentPower (c : Cfg) : Prog isa :=
  .seq (.block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++
    [.mov .esi (.mem (sc (c.sl T2))), decCounter])) (squarePower c)

def zeroMask (c : Cfg) (a : Nat) : List Instr :=
  c.nonzero a ++ [.mov .eax (.imm 0), .alu .sub .eax (.reg .edx), .mov .edx (.reg .eax), .alu .sub .edx (.imm 1)]

def descentChoose (c : Cfg) : Prog isa :=
  .seq (Mont.subCall c.SP (c.sl W0) (c.sl T3) (c.sl ONEP))
    (.block (zeroMask c (c.sl W0) ++ [.mov .ecx (.reg .edx)] ++
      sel (2 * c.n) (c.sl T4) (c.sl T1) (c.sl ONEP)))

def descentOps (c : Cfg) : List FOp :=
  [.mul (c.sl ACC) (c.sl ACC) (c.sl T4), .mul (c.sl T4) (c.sl T4) (c.sl T4),
    .mul (c.sl T0) (c.sl T0) (c.sl T4), .mul (c.sl T1) (c.sl T1) (c.sl T1)]

def descentCounter (c : Cfg) : List Instr :=
  [.mov .esi (.mem (sc (c.sl T2))), decCounter, .store (sc (c.sl T2)) .esi, testCounter]

def descentRound (c : Cfg) : Prog isa :=
  progs [descentPower c, descentChoose c, fprog c.SP (descentOps c), .block (descentCounter c)]

def tonelliPowers (c : Cfg) : Prog isa :=
  progs [rootPower c ((rootQ c + 1) / 2) 1,
    .block (copy (2 * c.n) (c.sl T5) (c.sl ACC)), rootPower c (rootQ c) 2]

def tonelliSetup (c : Cfg) : List Instr :=
  let zq := (Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)).val
  copy (2 * c.n) (c.sl T0) (c.sl ACC) ++ copy (2 * c.n) (c.sl ACC) (c.sl T5) ++
  setConst c.n (c.sl T1) (c.mont zq) ++ [.mov .eax (.imm 95), .store (sc (c.sl T2)) .eax]

def rootCandidate (c : Cfg) : Prog isa :=
  if c.C.p % 4 = 3 then rootPower c ((c.C.p + 1) / 4) 2
  else progs [tonelliPowers c, .block (tonelliSetup c), .loop (descentRound c) .ne]

def parityMask (c : Cfg) : List Instr :=
  [.mov .eax (.mem (sc (c.sl QY))), .mov .ecx (.mem (sc (c.sl D))),
    .alu .xor .ecx (.reg .eax), .alu .and .ecx (.imm 1), .mov .edx (.imm 0), .alu .sub .edx (.reg .ecx), .mov .ecx (.reg .edx)]

def selectRoot (c : Cfg) : Prog isa :=
  progs [Mont.mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE),
    Mont.subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY),
    .block (parityMask c ++ sel (2 * c.n) (c.sl QY) (c.sl QY) (c.sl W0))]

def checkRootOps (c : Cfg) : List FOp :=
  [.mul (c.sl QYM) (c.sl QY) (c.sl R2P), .mul (c.sl W1) (c.sl QYM) (c.sl QYM),
    .sub (c.sl W3) (c.sl W1) (c.sl W2)]

def invertMask : List Instr :=
  [.mov .edx (.reg .ecx), .alu .add .edx (.imm 1), .mov .eax (.imm 0), .alu .sub .eax (.reg .edx), .mov .edx (.reg .eax)]

def checkRootChecks (c : Cfg) : List Instr :=
  Ecdh.X86.Cfg.checkZero c (c.sl W3) ++ (parityMask c ++ (invertMask ++ c.andFlag))

def checkRoot (c : Cfg) : Prog isa :=
  .seq (fprog c.SP (checkRootOps c)) (.block (checkRootChecks c))

def decompressFinish (c : Cfg) : List Instr :=
  EcKey.X86.Cfg.finishWith c E QY

def recoverCoordinate (c : Cfg) : Prog isa :=
  .seq (rootCandidate c) (.seq (selectRoot c) (checkRoot c))

def decompress (c : Cfg) : Prog isa :=
  progs [.block (c.setupWith args), .block (decompressPeer c), fprog c.SP (rhsOps c),
    recoverCoordinate c, .block (decompressFinish c)]

end VG.Impl.EcKey.Compressed.X86
