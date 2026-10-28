module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Mgf1.X86_64
public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Calling the probable-prime test from the persistent generation frame

The test is a function of its own (`vg_dsa_probable_prime`), called with
the scratch base (frame word 5) as its working space, the unread rest of the
witness tape (words 13, 15 and 16), frame word 19 for the octets it reads,
and the candidate's size. Its status, 2 for a composite, is stored as the
generation's 3 in word 19, and the octets read are added to word 16 unless
the tape ran out. -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-- The test's arguments: `ws`, its words, the rest of the tape, `used` and
the size, `bits`. -/
def primeCallArgs (bits : Nat) : List Instr :=
  [.mov .rdi (.mem (sp 40)),
   .mov32 .rsi (.imm (BitVec.ofNat 32 (VG.Impl.Dsa.Generation.Layout.domainCheck / 8))),
   .mov .rdx (.mem (sp 104)), .alu .add .rdx (.mem (sp 128)),
   .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
   .mov .r8 (.reg .rsp), .alu .add .r8 (.imm 152), .mov32 .r9 (.imm (BitVec.ofNat 32 bits))]

/-- Add the octets read to the cursor if the tape sufficed, then store the
status, with 2 as 3. -/
def primeCallStatus : Prog isa :=
  .seq (.block [.alu .test .rax (.reg .rax)])
    (.seq (.ite .e (.block [])
        (.block [.mov .rcx (.mem (sp 152)), .alu .add .rcx (.mem (sp 128)), .store (sp 128) .rcx]))
      (.block [.mov .rcx (.reg .rax), .shift .shr .rcx 1, .alu .add .rax (.reg .rcx), .store (sp 152) .rax]))

/-- The status, returned in `eax`, then `primeCallStatus`. -/
def primeCallResult : Prog isa :=
  .seq (.block [.mov32 .rax (.reg .rax)]) primeCallStatus

/-- The test, `prime`, of a candidate of `bits` bits. -/
def primeCall (prime : Prog isa) (bits : Nat) : Prog isa :=
  .seq (.block (primeCallArgs bits)) (.seq prime primeCallResult)

end VG.Impl.Dsa.X86_64.Generation
