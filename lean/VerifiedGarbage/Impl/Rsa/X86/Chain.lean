module

public import VerifiedGarbage.Impl.Mont.X86

/-! Eight words per carry-chain iteration, with scalar iterations for the tail. -/

@[expose] public section
namespace VG.Impl.Rsa.X86.Chain
open VG VG.X86 VG.Impl.Mont.X86

def word (op : AluOp) (d : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp d)), .alu op .eax (.mem (at_ .ebx d)),
   .store (at_ .edi d) .eax]

def chunk (op : AluOp) (k : Nat) : List Instr :=
  [.alu .add .ecx (.reg .ecx)] ++ (List.range k).flatMap (fun j => word op (4*j)) ++
  [.alu .sbb .ecx (.reg .ecx), .alu .add .ebp (.imm (BitVec.ofNat 32 (4*k))),
   .alu .add .ebx (.imm (BitVec.ofNat 32 (4*k))),
   .alu .add .edi (.imm (BitVec.ofNat 32 (4*k))),
   .alu .sub .edx (.imm (BitVec.ofNat 32 (4*k)))]

def loop (op : AluOp) : Prog isa :=
  .loop (.seq (.block [.alu .cmp .edx (.imm 32)])
    (.seq (.ite .ae (.block (chunk op 8)) (.block (chunk op 1)))
      (.block [.alu .cmp .edx (.imm 0)]))) .ne

end VG.Impl.Rsa.X86.Chain
