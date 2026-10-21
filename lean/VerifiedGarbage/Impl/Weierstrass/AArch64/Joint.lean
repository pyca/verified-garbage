module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
public import VerifiedGarbage.Impl.Weierstrass.AArch64.FastNaf

/-! Interleaved public multiplication with five-bit peer and seven- or nine-bit generator digits. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open Jacobian

structure Cfg where
  K : WinCfg
  gBits : Nat
  onep : Nat
  tsym : String
  /-- The width of the generator's digits: seven, stored as bytes, or nine, as sixteen-bit
  words (`FastNaf.prep9`), for a table of `[m]G` for `m ≤ 256` at `tsym`. -/
  gw : Nat := 7

def Cfg.G (c : Cfg) : WinCfg := {c.K with bits := c.gBits}

def loadWords (dst count : Nat) : List Instr :=
  (List.range count).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (dst+8*i)]

/-- The generator's table stores the consecutive multiples `1, 2, …` in 64 bytes each, so the odd
multiple `2 a - 1` is at `128 (a - 1)`. -/
def address (c : Cfg) : List Instr :=
  [.subImm .x .x2 .x2 1,.lsl .x .x2 .x2 7,.adrSym .x16 c.tsym,
   .add .x .x16 .x16 .x2]

def fixedLoad (c : Cfg) : List Instr :=
  address c ++
  loadWords c.K.E.x 8 ++
  copy 4 c.K.E.z c.onep

/-- The generator's digit `x19`'s byte (its low byte for width nine) in `x2`, `x16` at its digits. -/
def fixedRead (c : Cfg) : List Instr :=
  if c.gw=9 then [.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x2 .x16 c.gBits]
  else Naf.digitRead c.G

/-- `x2 = (a + 1) / 2` for the digit's magnitude `a`: for width nine, from its low byte in `x2`
and its sign in its high byte. -/
def fixedIndex (c : Cfg) : List Instr :=
  if c.gw=9 then [.ldrb .x3 .x16 (c.gBits+1),.lsr .x .x3 .x3 7] ++ Naf.digitIndex.drop 1
  else Naf.digitIndex

/-- `x3` = the generator's digit `x19`'s sign. -/
def signRead (c : Cfg) : List Instr :=
  if c.gw=9 then [.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x3 .x16 (c.gBits+1),
    .lsr .x .x3 .x3 7]
  else Naf.signRead c.G

def signEntry (c : Cfg) : Prog isa :=
  .seq (.block (signRead c)) <|
  .ite (.nonzero .x .x3)
    (.block (Mont.AArch64.sub c.K.M c.K.E.y c.K.zero c.K.E.y)) (.block [])

def fixedEntry (c : Cfg) : Prog isa :=
  .seq (.block (fixedIndex c ++ fixedLoad c)) (signEntry c)

def fixedDigit (c : Cfg) (mixedAdd : Prog isa) : Prog isa :=
  .seq (.block (fixedRead c)) <|
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

/-- The generator's digits of `u`. -/
def gPrep (c : Cfg) (u : Nat) : Prog isa :=
  if c.gw=9 then FastNaf.prep9 c.G u else FastNaf.prep c.G u 7

def points (c : Cfg) (o : Ops) (u v : Nat) : Prog isa :=
  .seq (gPrep c u) <| .seq (FastNaf.prep c.K v 5) (window c o)

end VG.Impl.Weierstrass.AArch64.Joint
