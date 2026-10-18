module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate

/-! # Native seed attempts and the complete finite parameter search -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

def seedArguments (qLen : Nat) : List Instr :=
  [.mov .rax (.mem (sp 40)), .alu .add .rax (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q)),
   .store (sp 0) .rax, .mov .rax (.mem (sp 8)), .store (sp 216) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 224) .rax]

def successStatus : List Instr := [.mov .rax (.mem (sp 152)), .alu .cmp .rax (.imm 1)]

def onSuccess (next : Prog isa) : Prog isa :=
  .seq (.block successStatus) (.ite .e next (.block []))

def finishDomain (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (pack pLen qLen) (validate sq mul pLen qLen)

def seedAttempt (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (round : Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.block (seedArguments qLen))
    (.seq (subgroup G1 G256 mul round qLen)
      (onSuccess (.seq (primeSearch G1 G256 mul round pLen qLen)
        (onSuccess (.seq (generatorSearch sq mul pLen)
          (onSuccess (finishDomain sq mul pLen qLen)))))))

def parameterSearch (G1 G256 : Stream) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (round : Prog isa) (pLen qLen : Nat) : Prog isa :=
  tapeLoop seedTape qLen (seedAttempt G1 G256 sq mul round pLen qLen)

end VG.Impl.Dsa.X86_64.Generation
