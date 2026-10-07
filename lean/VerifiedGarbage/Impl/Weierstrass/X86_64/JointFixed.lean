import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf

/-! Direct generator-table lookup for public width-seven NAF digits. -/
namespace VG.Impl.Weierstrass.X86_64.Joint
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- The existing affine table has 64-byte entries for consecutive multiples. -/
def fixedAddress (tsym : String) : List Instr :=
  [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shl .rax 6,
   .leaSym .rdx tsym,.alu .add .rdx (.reg .rax)]

def fixedLoad (K : WinCfg) (tsym : String) : List Instr :=
  fixedAddress tsym ++
  Naf.copyPieces 4 (fun i => tblAt (16*i)) (fun i => sc (K.E.x+16*i)) ++
  setConst 4 K.E.z K.one

def fixedEntry (K : WinCfg) (tsym : String) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
    .ite .b (.block (fixedLoad K tsym)) (.block (
      [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      fixedLoad K tsym ++ VG.Impl.Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

end VG.Impl.Weierstrass.X86_64.Joint
