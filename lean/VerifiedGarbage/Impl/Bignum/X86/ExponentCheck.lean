module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Scan a public RSA exponent on i686

ESI points to the big-endian exponent and ECX is its nonzero byte length.
EBX accumulates the low word and EDX the high word, saturated at two.
Branches depend only on the public exponent and its length.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def exponentAccumulate : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .mov .ebp (.reg .ebx), .shift .shr .ebp 24,
   .shift .ror .edx 24, .alu .and .edx (.imm 0xffffff00), .alu .add .edx (.reg .ebp),
   .shift .ror .ebx 24, .alu .and .ebx (.imm 0xffffff00), .alu .add .ebx (.reg .eax),
   .mov .ebp (.reg .edx), .shift .shr .ebp 1, .alu .cmp .ebp (.imm 0)]

def exponentAdvance : List Instr :=
  [.alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def exponentConsume : Prog isa :=
  .seq (.block exponentAccumulate) (.ite .e (.block []) (.block [.mov .edx (.imm 2)]))

def exponentByte : Prog isa := .seq exponentConsume (.block exponentAdvance)

def exponentScan : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0), .mov .edx (.imm 0)]) (.loop exponentByte .ne)

def exponentBoundsTest : List Instr :=
  [.mov .ebp (.reg .edx), .shift .shr .ebp 1,
   .mov .eax (.reg .ebx), .alu .and .eax (.imm 1), .alu .xor .eax (.imm 1),
   .alu .or .ebp (.reg .eax), .alu .cmp .ebp (.imm 0)]

def exponentOneTest : List Instr :=
  [.mov .ebp (.reg .ebx), .alu .xor .ebp (.imm 1), .alu .or .ebp (.reg .edx),
   .alu .cmp .ebp (.imm 0)]

def exponentResult (b : Bool) : Prog isa := .block [.mov .eax (.imm (BitVec.ofNat 32 b.toNat))]

def exponentTest : Prog isa :=
  .seq (.block exponentBoundsTest)
    (.ite .e
      (.seq (.block exponentOneTest) (.ite .e (exponentResult false) (exponentResult true)))
      (exponentResult false))

def exponentCheck : Prog isa := .seq exponentScan exponentTest

end VG.Impl.Bignum.X86
