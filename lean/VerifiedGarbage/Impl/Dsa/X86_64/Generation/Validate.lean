module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate

/-! # Validate the packed generated domain using the existing verified checker -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def validateArgs (pLen qLen : Nat) : List Instr :=
  [.mov .rdi (.mem (sp 40)), .mov .r8 (.reg .rdi),
   .alu .add .rdi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.packed)),
   .alu .add .r8 (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.domainCheck)),
   .mov32 .rdx (.imm (BitVec.ofNat 32 pLen)), .mov32 .rcx (.imm (BitVec.ofNat 32 qLen))]

def validate (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.seq (.block (validateArgs pLen qLen)) (Generate.checkParameters sq mul))
    (.seq (.block [.alu .test .rax (.reg .rax)])
      (.ite .e (.block (stackStatus 3)) (.block (stackStatus 1))))

end VG.Impl.Dsa.X86_64.Generation
