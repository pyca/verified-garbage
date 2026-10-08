import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Impl.Weierstrass.X86.TCombJ
import VerifiedGarbage.Impl.Weierstrass.X86.Window

/-! Width-five NAF multiplication for public P-256 verification scalars. -/
namespace VG.Impl.Weierstrass.X86.Naf
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open Jacobian

/-- The double used to build the eight odd multiples follows the table. -/
def twice (K : WinCfg) : Pt := K.tblPt 9

/-- Copy adjacent 16-byte pieces between public addresses. -/
def copyPieces (n : Nat) (src dst : Nat → MemOp) : List Instr :=
  (List.range n).flatMap fun i => [.movdquLoad (selAcc i) (src i),.movdquStore (dst i) (selAcc i)]

/-- Address of entry `eax`, indexed from zero, in `edx`. -/
def tableAddress (tbl : Nat) : List Instr :=
  [.mov .ecx (.imm 96),.mul .ecx,.mov .edx (.reg .edi),
   .alu .add .edx (.imm (BitVec.ofNat 32 tbl)),.alu .add .edx (.reg .eax)]

/-- Store `R` in entry `esi`, indexed from zero. -/
def tableStore (K : WinCfg) : List Instr :=
  [.mov .eax (.reg .esi)] ++ tableAddress K.tbl ++
  copyPieces 6 (fun i => sc (K.R.x+16*i)) (fun i => TCombCfg.tblAt (16*i))

def tableStep (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (jacAdd K F K.R (twice K) K.D) <|
    .block (copyPt 4 K.R K.D ++ tableStore K ++
      [.alu .add .esi (.imm 1),.alu .cmp .esi (.imm 8)])

def table (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (fprog F (dblJMul K.S K.P (twice K))) <|
  .seq (.block (copyPt 4 (K.tblPt 1) K.P ++ copyPt 4 K.R K.P ++ [.mov .esi (.imm 1)])) <|
    .loop (tableStep K F) .b

def digitRead (K : WinCfg) : List Instr :=
  [.mov .ecx (.reg .edi),.alu .add .ecx (.reg .esi),
   .movzx8 .ebx (winByte K.bits),.alu .test .ebx (.reg .ebx)]

/-- Read the odd multiple whose nonzero magnitude is in `ebx`. -/
def publicEntry (K : WinCfg) : List Instr :=
  [.mov .eax (.reg .ebx),.alu .sub .eax (.imm 1),.shift .shr .eax 1] ++ tableAddress K.tbl ++
  copyPieces 6 (fun i => TCombCfg.tblAt (16*i)) (fun i => sc (K.E.x+16*i))

def signedEntry (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block [.alu .cmp .ebx (.imm 128)]) <|
    .ite .b (.block (publicEntry K)) (.seq (.block (
      [.mov .eax (.imm 256),.alu .sub .eax (.reg .ebx),.mov .ebx (.reg .eax)] ++
      publicEntry K)) (opCode F (.sub K.E.y K.zero K.E.y)))

def digit (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (digitRead K)) <|
    .ite .e (.block []) (.seq (signedEntry K F) <|
      .seq (jacAdd K F K.R K.E K.D) (.block (copyPt 4 K.R K.D)))

def windowStep (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <|
  .seq (fprog F (dblJMul K.S K.R K.D)) <|
  .seq (.block (copyPt 4 K.R K.D)) <|
  .seq (digit K F) (.block [.alu .test .esi (.reg .esi)])

/-- The multiplication loop leaves its result in Jacobian coordinates. -/
def window (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (table K F) <|
    .seq (.block (infinity K K.R ++ [.mov .esi (.imm 256)])) <|
      .seq (digit K F) (.loop (windowStep K F) .ne)

/-- Convert once to the homogeneous coordinates consumed by verification. -/
def finish (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (VG.Impl.Weierstrass.X86.WinCfg.tc K F).outFix) (fprog F (VG.Impl.Weierstrass.X86.WinCfg.tc K F).outOps)

end VG.Impl.Weierstrass.X86.Naf
