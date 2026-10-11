module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
public import VerifiedGarbage.Impl.Weierstrass.AArch64.FastNaf

/-! Interleaved public multiplication with five-bit peer and seven-bit generator digits. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

structure Cfg where
  K : WinCfg
  gBits : Nat
  onep : Nat
  tsym : String

def Cfg.G (c : Cfg) : WinCfg := {c.K with bits := c.gBits}

def loadWords (dst count : Nat) : List Instr :=
  (List.range count).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (dst+8*i)]

/-- The existing generator table's first row stores the consecutive multiples 1..64. -/
def address (c : Cfg) : List Instr :=
  [.subImm .x .x2 .x2 1,.lsl .x .x2 .x2 7,.adrSym .x16 c.tsym,
   .add .x .x16 .x16 .x2]

def fixedLoad (c : Cfg) : List Instr :=
  address c ++
  loadWords c.K.E.x 8 ++
  copy 4 c.K.E.z c.onep

def signEntry (c : Cfg) : Prog isa :=
  .seq (.block (Naf.signRead c.G)) <|
  .ite (.nonzero .x .x3)
    (.block (Mont.AArch64.sub c.K.M c.K.E.y c.K.zero c.K.E.y)) (.block [])

def fixedEntry (c : Cfg) : Prog isa :=
  .seq (.block (Naf.digitIndex ++ fixedLoad c)) (signEntry c)

def fixedDigit (c : Cfg) (mixedAdd : Prog isa) : Prog isa :=
  .seq (.block (Naf.digitRead c.G)) <|
  .ite (.nonzero .x .x2)
    (.seq (fixedEntry c) (.seq mixedAdd (.block (copyPt 4 c.K.R c.K.D)))) (.block [])

/-- Arithmetic helpers may supply verified forwarding and cached coordinates. -/
structure Ops where
  table : Prog isa
  cache : Prog isa
  digitQ : Prog isa
  double : Prog isa
  mixedAdd : Prog isa

def digits (c : Cfg) (o : Ops) : Prog isa :=
  .seq o.digitQ (fixedDigit c o.mixedAdd)

def step (c : Cfg) (o : Ops) : Prog isa :=
  .seq (.block [decCounter]) (.seq o.double (digits c o))

def run (c : Cfg) (o : Ops) : Prog isa :=
  .seq (digits c o) (.loop (step c o) (.nonzero .x .x19))

def window (c : Cfg) (o : Ops) : Prog isa :=
  .seq o.table <| .seq o.cache <|
  .seq (.block (infinity c.K c.K.R ++ [.movz .x .x19 256 0])) <|
  .seq (run c o) (jacFinish c.K)

def points (c : Cfg) (o : Ops) (u v : Nat) : Prog isa :=
  .seq (FastNaf.prep c.G u 7) <| .seq (FastNaf.prep c.K v 5) (window c o)

end VG.Impl.Weierstrass.AArch64.Joint
