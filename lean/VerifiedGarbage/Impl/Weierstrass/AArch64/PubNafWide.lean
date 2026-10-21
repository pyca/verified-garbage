module
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Impl.Weierstrass.AArch64.FastNaf
@[expose] public section
namespace VG.Impl.Weierstrass.AArch64.PubNafWide
open VG.Impl.Mont.AArch64 (loads)
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 PubNaf
/-- Width-seven initialization, using the same multiword subtract-and-shift loop. -/
def prepInit7 (K : WinCfg) (src : Nat) : List Instr :=
  loads (low K.M.n) src ++
  [.movz .x (top K.M.n) 0 0, .movz .x (cst K.M.n 0) 127 0, .movz .x (cst K.M.n 1) 64 0,
   .movz .x (cst K.M.n 2) 0 0, .movz .x (cst K.M.n 3) 1 0,
   .movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n + 1)) 0, .addImm .x .x20 .x0 K.bits]
def prep7 (K : WinCfg) (src : Nat) : Prog isa :=
 .seq (.block (prepInit7 K src)) (.loop (prepStep K.M.n) (.nonzero .x .x19))
/-- Width-nine initialization: the digit's mask `511` and sign bit `256`. -/
def prepInit9 (K : WinCfg) (src : Nat) : List Instr :=
  loads (low K.M.n) src ++
  [.movz .x (top K.M.n) 0 0, .movz .x (cst K.M.n 0) 511 0, .movz .x (cst K.M.n 1) 256 0,
   .movz .x (cst K.M.n 2) 0 0, .movz .x (cst K.M.n 3) 1 0,
   .movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n + 1)) 0, .addImm .x .x20 .x0 K.bits]
/-- A digit of width nine as a sixteen-bit word, in two bytes: the model has no halfword store. -/
def store9 : List Instr := FastNaf.store16 ++ ([.addImm .x .x20 .x20 2] : List Instr)
def prepStep9 (n : Nat) : Prog isa :=
  .seq (chooseDigit n) (.block (store9 ++ subtractShift n ++ [decCounter]))
/-- The `64 n + 1` signed digits of width nine of the scalar at `src`, as sixteen-bit words from
`K.bits`. -/
def prep9 (K : WinCfg) (src : Nat) : Prog isa :=
 .seq (.block (prepInit9 K src)) (.loop (prepStep9 K.M.n) (.nonzero .x .x19))
/-- Public width-five or width-seven recoding; the width is fixed at emission. -/
def prep (K : WinCfg) (src w : Nat) : Prog isa :=
 if w=7 then prep7 K src else PubNaf.prep K src
end VG.Impl.Weierstrass.AArch64.PubNafWide
