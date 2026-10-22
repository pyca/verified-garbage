module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Chain
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.EcKey.AArch64

/-! # Shared SEC 1 coordinate recovery on AArch64

Fixed exponents use the existing verified sliding-window power code.
Only P-224 needs the two-adic descent after exponentiation.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.AArch64

open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP QXM QYM QY W0 W1 W2 W3)

def rootQ (c : Cfg) : Nat := (c.C.p - 1) / 2 ^ 96

/-- Preserve the tag, then accept precisely 02 and 03. -/
def decompressTag (c : Cfg) : List Instr :=
  [zero7, .ldrb .x1 .x6 0, st .x1 (c.sl D), .movz .x .x5 1 0,
    .logic .orr .x .x1 .x1 .x5, .movz .x .x5 3 0,
    .logic .eor .x .x1 .x1 .x5] ++ Ecdh.AArch64.Cfg.isZero

def decompressPeer (c : Cfg) : List Instr :=
  (Ecdh.AArch64.Cfg.consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  decompressTag c ++ c.andFlag ++ Ecdh.AArch64.Cfg.checkLtP c (c.sl E)

def rhsOps (c : Cfg) : List FOp :=
  [.mul (c.sl QXM) (c.sl E) (c.sl R2P),
    .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM),
    .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1),
    .add (c.sl W2) (c.sl W3) (c.sl BP)]

/-- Reuse the inversion power's workspace, field backend and exponent chain. -/
def rootChain (c : Cfg) (e : Nat) : ChainCfg :=
  .ofExp c.MP' (c.sl ACC) (c.sl W2) (c.sl RX) e

def rootPower (c : Cfg) (e : Nat) : Prog isa := Chain.pow (rootChain c e)

def squareStep (c : Cfg) (slot : Nat) : Prog isa :=
  .block (opCode c.MP' (.mul (c.sl slot) (c.sl slot) (c.sl slot)) ++ [decCounter])

def squarePower (c : Cfg) : Prog isa :=
  .ite (.zero .x .x19) (.block []) (.loop (squareStep c T3) (.nonzero .x .x19))

def descentPower (c : Cfg) : Prog isa :=
  .seq (.block (copy c.n (c.sl T3) (c.sl T0) ++
    [decCounter])) (squarePower c)

def descentChoose (c : Cfg) : List Instr :=
  opCode c.MP' (.sub (c.sl W0) (c.sl T3) (c.sl ONEP)) ++
  Ecdh.AArch64.Cfg.zero c (c.sl W0) ++ [.addImm .x .x3 .x2 0] ++
  sel c.n (c.sl T4) (c.sl T1) (c.sl ONEP)

def descentOps (c : Cfg) : List FOp :=
  [.mul (c.sl ACC) (c.sl ACC) (c.sl T4),
    .mul (c.sl T4) (c.sl T4) (c.sl T4),
    .mul (c.sl T0) (c.sl T0) (c.sl T4),
    .mul (c.sl T1) (c.sl T1) (c.sl T1)]

def descentCounter : List Instr :=
  [.umov .x .x19 .v27 0, decCounter]

def descentBody (c : Cfg) : Prog isa :=
  progs [descentPower c, .block (descentChoose c), fprogB c.MP' (descentOps c)]

def descentRound (c : Cfg) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v27 0 .x19)])
    (.seq (descentBody c) (.block descentCounter))

def tonelliPowers (c : Cfg) : Prog isa :=
  progs [rootPower c ((rootQ c + 1) / 2),
    .block (copy c.n (c.sl T5) (c.sl ACC)), rootPower c (rootQ c)]

def tonelliSetup (c : Cfg) : List Instr :=
  let zq := (Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)).val
  copy c.n (c.sl T0) (c.sl ACC) ++ copy c.n (c.sl ACC) (c.sl T5) ++
  setConst c.n (c.sl T1) (c.mont zq) ++ [.movz .x .x19 95 0]

def rootCandidate (c : Cfg) : Prog isa :=
  if c.C.p % 4 = 3 then rootPower c ((c.C.p + 1) / 4)
  else progs [tonelliPowers c, .block (tonelliSetup c),
    .loop (descentRound c) (.nonzero .x .x19)]

/-- All ones exactly when canonical y has the wrong parity. -/
def parityMask (c : Cfg) : List Instr :=
  [ld .x1 (c.sl QY), ld .x2 (c.sl D), .logic .eor .x .x2 .x2 .x1,
    .movz .x .x1 1 0, .logic .and .x .x2 .x2 .x1,
    zero7, .sub .x .x3 .x7 .x2]

def selectRoot (c : Cfg) : Prog isa :=
  progs [opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE)),
    .block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0))]

def checkRootOps (c : Cfg) : List FOp :=
  [.mul (c.sl QYM) (c.sl QY) (c.sl R2P),
    .mul (c.sl W1) (c.sl QYM) (c.sl QYM),
    .sub (c.sl W3) (c.sl W1) (c.sl W2)]

def invertMask : List Instr :=
  [zero7, .addImm .x .x2 .x3 1, .sub .x .x2 .x7 .x2]

def checkRootChecks (c : Cfg) : List Instr :=
  Ecdh.AArch64.Cfg.checkZero c (c.sl W3) ++ (parityMask c ++ (invertMask ++ c.andFlag))

def checkRoot (c : Cfg) : Prog isa :=
  .seq (fprogB c.MP' (checkRootOps c)) (.block (checkRootChecks c))

def decompressFinish (c : Cfg) : List Instr := EcKey.AArch64.Cfg.finishWith c E QY

def recoverCoordinate (c : Cfg) : Prog isa :=
  .seq (rootCandidate c) (.seq (selectRoot c) (checkRoot c))

def decompress (c : Cfg) : Prog isa :=
  progs [.block args, .block (c.setupWith none), .block (decompressPeer c),
    fprogB c.MP' (rhsOps c), recoverCoordinate c, .block (decompressFinish c)]

end VG.Impl.EcKey.Compressed.AArch64
