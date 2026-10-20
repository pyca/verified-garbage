module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial

/-! # Trial division by the initialized small-prime table

ESI points to the big-endian candidate and EDI to the reciprocal table.
The helper returns one if no table entry divides the candidate, zero
otherwise. Candidate-dependent early rejection is permitted for public
parameter generation. Its small frame holds the source, table and index.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def trialSp (d : Nat) : MemOp := at_ .esp d

def trialCheckEntry : List Instr :=
  [.store (trialSp 0) .esi, .store (trialSp 4) .edi, .mov .eax (.imm 0), .store (trialSp 8) .eax,
   .mov .eax (.imm 1), .store (trialSp 12) .eax]

def trialCheckArgs (len : Nat) : List Instr :=
  [.mov .eax (.mem (trialSp 8)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (.mem (trialSp 4)),
   .mov .esi (.mem (at_ .eax 0)), .mov .edi (.mem (at_ .eax 4)),
   .mov .ebp (.mem (trialSp 0)), .mov .ecx (.imm (BitVec.ofNat 32 (len / 2)))]

def trialCheckReject : List Instr :=
  [.mov .eax (.imm 0), .store (trialSp 12) .eax, .alu .cmp .eax (.imm 0)]

def trialCheckNext (entries : Nat) : List Instr :=
  [.mov .eax (.mem (trialSp 8)), .alu .add .eax (.imm 1), .store (trialSp 8) .eax,
   .alu .cmp .eax (.imm (BitVec.ofNat 32 entries))]

def trialCheckStep (len entries : Nat) : Prog isa :=
  .seq (.block (trialCheckArgs len))
    (.seq trialReduce (.seq (.block [.alu .cmp .ebx (.imm 0)])
      (.ite .e (.block trialCheckReject) (.block (trialCheckNext entries)))))

def trialCheckBody (len entries : Nat) : Prog isa :=
  .seq (.block trialCheckEntry)
    (.seq (.loop (trialCheckStep len entries) .ne) (.block [.mov .eax (.mem (trialSp 12))]))

def trialCheck (len entries : Nat) : Prog isa :=
  .frame (.alloc 16) (trialCheckBody len entries) (.free 16)
end VG.Impl.Dsa.X86.Generation
