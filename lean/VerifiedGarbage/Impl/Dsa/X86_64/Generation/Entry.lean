module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Generate

/-! # System V entry for DSA parameter generation

The outer 48 bytes save the six callee-saved registers. The inner 296-byte
frame holds the persistent search state and aligns nested calls. Incoming
stack arguments start 352 bytes above the inner frame's stack pointer.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def savedRegisters : List (Nat × Reg) :=
  [(0, .rbx), (8, .rbp), (16, .r12), (24, .r13), (32, .r14), (40, .r15)]

def saveRegisters : List Instr := savedRegisters.map fun (offset, reg) => .store (sp offset) reg

def restoreRegisters : List Instr := savedRegisters.map fun (offset, reg) => .mov reg (.mem (sp offset))

def entryHeader : List Instr :=
  [.store (sp 48) .rdi, .store (sp 56) .rsi,
   .store (sp 136) .rdx, .store (sp 144) .rcx, .store (sp 224) .rcx,
   .store (sp 64) .r8, .store (sp 72) .r9]

def incomingSlots : List (Nat × Nat) := [(352, 88), (360, 96), (368, 104), (376, 120), (384, 40)]

def entryIncoming : List Instr := incomingSlots.flatMap fun (src, dst) =>
  [.mov .rax (.mem (sp src)), .store (sp dst) .rax]

def derivedSlots : List (Nat × Nat) :=
  [(24, VG.Impl.Dsa.Generation.Layout.wrappedSeed),
   (32, VG.Impl.Dsa.Generation.Layout.hashes),
   (112, VG.Impl.Dsa.Generation.Layout.hash)]

def entryDerived : List Instr :=
  (derivedSlots.flatMap fun (dst, offset) =>
    [.mov .rax (.mem (sp 40)), .alu .add .rax (.imm (BitVec.ofNat 32 offset)), .store (sp dst) .rax]) ++
  [.mov32 .rax (.imm 0), .store (sp 128) .rax]

def dispatch (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp 136)), .alu .cmp .rax (.imm 128)])
    (.ite .e (generate G1 G256 sq mul round 128 20)
      (.seq (.block [.alu .cmp .rax (.imm 256)])
        (.ite .e (generate G1 G256 sq mul round 256 32) (generate G1 G256 sq mul round 384 32))))

def entryBody (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (.block (entryHeader ++ entryIncoming ++ entryDerived)) (dispatch G1 G256 sq mul round)

def code (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block saveRegisters)
      (.seq (.frame (.alloc 296) (entryBody G1 G256 sq mul round) (.free 296)) (.block restoreRegisters)))
    (.free 48)

end VG.Impl.Dsa.X86_64.Generation
