import VerifiedGarbage.Impl.P256.VerifyDouble
import VerifiedGarbage.Impl.Weierstrass.JacAdd
import VerifiedGarbage.Impl.Weierstrass.AArch64.Window
import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-!
P-256 verification with public scalar digits and Jacobian accumulators.
All exceptional-point branches and table indices depend on public verification data.
This implementation is not used for secret scalars.
-/
namespace VG.Impl.Weierstrass.AArch64.Jacobian
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | p::ps => .seq p (seqs ps)

def infinity (K : WinCfg) (o : Pt) : List Instr :=
  setConst K.M.n o.x 0 ++ setConst K.M.n o.y K.one ++ setConst K.M.n o.z 0

def jacAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroMask K.M.n p.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroMask K.M.n q.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt K.M.n o p)) <|
  .seq (fprogB K.M (jacHead K.S p q)) <|
  .seq (.block (zeroMask K.M.n K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask K.M.n K.S.t5)) <|
      .ite (.nonzero .x .x2) (VG.Impl.P256.VerifyDouble.double K.M K.S p o) (.block (infinity K o)))
    (fprogB K.M (jacTail K.S p q o))

def tablePt (K : WinCfg) (i : Nat) : Pt :=
  ⟨K.tbl+96*(i-1),K.tbl+96*(i-1)+32,K.tbl+96*(i-1)+64⟩

def tableStore (K : WinCfg) : List Instr :=
  (List.range 12).flatMap fun i => [ld .x4 (K.R.x+8*i), .str .x .x4 .x20 (8*i)]

def jacTreeFetch (K : WinCfg) (h : Nat) : List Instr := [.movz .x .x17 (BitVec.ofNat 16 (h-1)) 0, .sub .x .x17 .x17 .x19,
    .lsr .x .x17 .x17 1, .movz .x .x2 96 0, .mul .x .x17 .x17 .x2,
    .addImm .x .x16 .x0 K.tbl, .add .x .x16 .x16 .x17] ++
    ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i),st .x4 (K.E.x+8*i)])

def jacTreeArithmetic (K : WinCfg) (h : Nat) : Prog isa :=
  .seq (.block [.movz .x .x5 1 0, .logic .and .x .x2 .x19 .x5]) <|
    .ite (.nonzero .x .x2)
      (.seq (.block (jacTreeFetch K h)) (VG.Impl.P256.VerifyDouble.double K.M K.S K.E K.D))
      (jacAdd K K.R K.P K.D)

def jacTreeStep (K : WinCfg) (h : Nat) : Prog isa :=
  .seq (jacTreeArithmetic K h) <|
    .block (copyPt 4 K.R K.D ++ tableStore K ++
      [.addImm .x .x20 .x20 96,decCounter])

def jacBuildTree (K : WinCfg) (h : Nat) : Prog isa :=
  .seq (.block (copyPt 4 K.R K.P ++ [.addImm .x .x20 .x0 K.tbl] ++ tableStore K ++
    [.addImm .x .x20 .x20 96, .movz .x .x19 (BitVec.ofNat 16 (h-1)) 0])) <|
  .loop (jacTreeStep K h) (.nonzero .x .x19)

def publicEntry (K : WinCfg) : List Instr :=
  [.subImm .x .x2 .x2 1, .movz .x .x17 96 0, .mul .x .x2 .x2 .x17,
   .addImm .x .x16 .x0 K.tbl, .add .x .x16 .x16 .x2] ++
  ((List.range 12).flatMap fun i => [.ldr .x .x4 .x16 (8*i), st .x4 (K.E.x+8*i)])

def jacDoubles (K : WinCfg) (w : Nat) : Prog isa :=
  let ds := (List.range w).map fun i =>
    if i%2==0 then VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D else VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R
  seqs (ds ++ if w%2==1 then [.block (copyPt 4 K.R K.D)] else [])

def jacSignedAdd (K : WinCfg) (w : Nat) : Prog isa :=
  .seq (.block (publicEntry K ++ negYW K.M w K.neg K.zero K.E.y K.bits)) <|
    .seq (jacAdd K K.R K.E K.D) (.block (copyPt 4 K.R K.D))

def jacDigitAdd (K : WinCfg) (w : Nat) : Prog isa :=
  .seq (.block (winIndex w ++ hornerBits K.bits w ++ magnitudeH (2^(w-1)))) <|
    .ite (.nonzero .x .x2) (jacSignedAdd K w) (.block [])

def jacStep (K : WinCfg) (w : Nat) : Prog isa :=
  .seq (.block [decCounter]) <| .seq (jacDoubles K w) (jacDigitAdd K w)

def jacFinish (K : WinCfg) : Prog isa :=
  .seq (.seq (fprogB K.M (fromJ K.S K.R (WinCfg.zeroPt K) K.E))
    (.block (copyPt 4 K.R K.E))) (.block (WinCfg.ySel {K with E := K.R}))

def jacWindow (K : WinCfg) (w : Nat) : Prog isa :=
  let j := (256+w)/w
  let step := jacStep K w
  .seq (jacBuildTree K (2^(w-1))) <|
    .seq (.block (infinity K K.R ++ [.movz .x .x19 (BitVec.ofNat 16 j) 0])) <|
    .seq (.loop step (.nonzero .x .x19)) (jacFinish K)

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

def jacCombSum (K : TCombCfg) : Prog isa :=
  .seq (jacMixedAdd (combWinCfg K) K.A K.E K.D) (.block (copyPt 4 K.A K.D))

def jacCombStep (K : TCombCfg) : Prog isa :=
  let add := .seq (.block (K.selectPublic ++ negYW K.M K.w K.neg K.zero K.E.y K.bits))
    (jacCombSum K)
  .seq (.block (decCounter :: K.digit)) (.ite (.nonzero .x .x2) add (.block []))

def jacCombLoop (K : TCombCfg) : Prog isa :=
  .seq (.block K.init) (.loop (jacCombStep K) (.nonzero .x .x19))

def jacCombFinish (K : TCombCfg) : Prog isa :=
  .seq (.seq (fprogB K.M (fromJ K.S K.A (WinCfg.zeroPt (combWinCfg K)) K.E))
    (.block (copyPt 4 K.A K.E))) (.block (WinCfg.ySel {combWinCfg K with E := K.A}))

def jacComb (K : TCombCfg) : Prog isa :=
  .seq (jacCombLoop K) (jacCombFinish K)

end VG.Impl.Weierstrass.AArch64.Jacobian
