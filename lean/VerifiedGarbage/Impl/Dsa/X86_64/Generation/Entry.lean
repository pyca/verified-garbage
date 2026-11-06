module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output

/-! # System V entry for DSA parameter generation

The outer 48 bytes save the six callee-saved registers. The inner 296-byte
frame holds the persistent search state and aligns nested calls. Incoming
stack arguments start 352 bytes above the inner frame's stack pointer.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}


def savedRegisters : List (Nat × Reg) :=
  [(0, .rbx), (8, .rbp), (16, .r12), (24, .r13), (32, .r14), (40, .r15)]

def saveRegisters : List Instr := savedRegisters.map fun (offset, reg) => .store (sp offset) reg

def restoreRegisters : List Instr := savedRegisters.map fun (offset, reg) => .mov reg (.mem (sp offset))

def derivedSlots : List (Nat × Nat) :=
  [(24, VG.Impl.Dsa.Generation.Layout.wrappedSeed),
   (32, VG.Impl.Dsa.Generation.Layout.hashes),
   (112, VG.Impl.Dsa.Generation.Layout.hash)]

def entryDerived : List Instr :=
  (derivedSlots.flatMap fun (dst, offset) =>
    [.mov .rax (.mem (sp 40)), .alu .add .rax (.imm (BitVec.ofNat 32 offset)), .store (sp dst) .rax]) ++
  [.mov32 .rax (.imm 0), .store (sp 128) .rax]

end VG.Impl.Dsa.X86_64.Generation
