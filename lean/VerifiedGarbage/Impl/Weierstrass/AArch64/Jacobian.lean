module

public import VerifiedGarbage.Impl.P256.VerifyDouble
public import VerifiedGarbage.Impl.Weierstrass.JacAdd

/-!
P-256 verification with public scalar digits and Jacobian accumulators.
All exceptional-point branches and table indices depend on public verification data.
This implementation is not used for secret scalars.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Jacobian
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

def infinity (K : WinCfg) (o : Pt) : List Instr :=
  setConst K.M.n o.x 0 ++ setConst K.M.n o.y K.one ++ setConst K.M.n o.z 0

def tablePt (K : WinCfg) (i : Nat) : Pt :=
  ⟨K.tbl+96*(i-1),K.tbl+96*(i-1)+32,K.tbl+96*(i-1)+64⟩

def tableStore (K : WinCfg) : List Instr :=
  (List.range 12).flatMap fun i => [ld .x4 (K.R.x+8*i), .str .x .x4 .x20 (8*i)]

def publicEntry (K : WinCfg) : List Instr :=
  [.subImm .x .x2 .x2 1, .movz .x .x17 96 0, .mul .x .x2 .x2 .x17,
   .addImm .x .x16 .x0 K.tbl, .add .x .x16 .x16 .x2] ++
  ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i), st .x4 (K.E.x+8*i)])

def jacFinish (K : WinCfg) : Prog isa :=
  .seq (.seq (fprogB K.M (fromJ K.S K.R (WinCfg.zeroPt K) K.E))
    (.block (copyPt 4 K.R K.E))) (.block (WinCfg.ySel {K with E := K.R}))

def jacMixedAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  let head := jacMixedHead K.S p q
  let tail := jacMixedTail K.S p q o
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (fprogB K.M head) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (fprogB K.M tail)

/-- The comb uses the same scratch layout as the public Jacobian window. -/
def combWinCfg (K : TCombCfg) : WinCfg :=
  ⟨K.M,K.S,K.E,K.A,K.E,K.D,K.neg,K.zero,K.bits,0,K.J,K.one⟩

def jacCombFinish (K : TCombCfg) : Prog isa :=
  .seq (.seq (fprogB K.M (fromJ K.S K.A (WinCfg.zeroPt (combWinCfg K)) K.E))
    (.block (copyPt 4 K.A K.E))) (.block (WinCfg.ySel {combWinCfg K with E := K.A}))

end VG.Impl.Weierstrass.AArch64.Jacobian
