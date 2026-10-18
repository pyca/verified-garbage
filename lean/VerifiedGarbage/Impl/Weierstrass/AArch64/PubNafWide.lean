module
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
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
/-- Public width-five or width-seven recoding; the width is fixed at emission. -/
def prep (K : WinCfg) (src w : Nat) : Prog isa :=
 if w=7 then prep7 K src else PubNaf.prep K src
end VG.Impl.Weierstrass.AArch64.PubNafWide
