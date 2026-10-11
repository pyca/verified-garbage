module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep

/-! Width-five NAF multiplication for public verification scalars. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open Jacobian

/-- The double used to build the eight odd multiples follows the table. -/
def twice (K : WinCfg) : Pt := K.tblPt 9

/-- Copy adjacent 16-byte pieces between public addresses. -/
def copyPieces (n : Nat) (src dst : Nat → MemOp) : List Instr :=
  (List.range n).flatMap fun i => [.movdquLoad (selAcc i) (src i),.movdquStore (dst i) (selAcc i)]

/-- Piece `i` of a `24 n`-byte entry: `16 i`, but the last at its last 16 bytes. -/
def pieceOff (n i : Nat) : Nat := if i + 1 < (3 * n + 1) / 2 then 16 * i else 24 * n - 16

/-- Address of entry `rax`, indexed from zero, of a table of `24 n`-byte
entries, in `rdx`. -/
def tableAddress (n tbl : Nat) : List Instr :=
  [.mov32 .rcx (.imm (BitVec.ofNat 32 (24*n))),.mul .rcx,.mov .rdx (.reg .rdi),
   .alu .add .rdx (.imm (BitVec.ofNat 32 tbl)),.alu .add .rdx (.reg .rax)]

/-- Store `R` in entry `rbx`, indexed from zero. -/
def tableStore (K : WinCfg) : List Instr :=
  [.mov .rax (.reg .rbx)] ++ tableAddress K.M.n K.tbl ++
  copyPieces ((3*K.M.n+1)/2) (fun i => sc (K.R.x+pieceOff K.M.n i)) (fun i => tblAt (pieceOff K.M.n i))

def tableStep (K : WinCfg) : Prog isa :=
  .seq (jacAdd K K.R (twice K) K.D) <|
    .block (copyPt K.M.n K.R K.D ++ tableStore K ++
      [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)])

def table (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (dblJMul K.S K.P (twice K))) <|
  .seq (.block (copyPt K.M.n (K.tblPt 1) K.P ++ copyPt K.M.n K.R K.P ++ [.mov32 .rbx (.imm 1)])) <|
    .loop (tableStep K) .b

def digitRead (K : WinCfg) : List Instr :=
  [.movzx8 .r8 (tbl K.bits),.alu .test .r8 (.reg .r8)]

/-- Read the odd multiple whose nonzero magnitude is in `r8`. -/
def publicEntry (K : WinCfg) : List Instr :=
  [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shr .rax 1] ++ tableAddress K.M.n K.tbl ++
  copyPieces ((3*K.M.n+1)/2) (fun i => tblAt (pieceOff K.M.n i)) (fun i => sc (K.E.x+pieceOff K.M.n i))

def signedEntry (K : WinCfg) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
    .ite .b (.block (publicEntry K)) (.block (
      [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      publicEntry K ++ Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

def digit (K : WinCfg) : Prog isa :=
  .seq (.block (digitRead K)) <|
    .ite .e (.block []) (.seq (signedEntry K) <|
      .seq (jacAdd K K.R K.E K.D) (.block (copyPt K.M.n K.R K.D)))

def windowStep (K : WinCfg) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <|
  .seq (fprogB K.M (dblJMul K.S K.R K.D)) <|
  .seq (.block (copyPt K.M.n K.R K.D)) <|
  .seq (digit K) (.block [.alu .test .rbx (.reg .rbx)])

/-- The result remains in Jacobian coordinates for the final verification sum. -/
def window (K : WinCfg) : Prog isa :=
  .seq (table K) <|
    .seq (.block (infinity K K.R ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*K.M.n)))])) <|
      .seq (digit K) (.loop (windowStep K) .ne)

end VG.Impl.Weierstrass.X86_64.Naf
