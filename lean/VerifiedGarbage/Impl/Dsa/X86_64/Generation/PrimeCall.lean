module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Mgf1.X86_64
public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Calling the probable-prime test from the persistent generation frame

The tests are functions of their own (`vg_dsa_probable_prime_{bits}`),
called with the scratch base (frame word 5) as their working space, the
unread rest of the witness tape (words 13, 15 and 16) and frame word 19 for
the octets they read. Their status, 2 for a composite, is stored as the
generation's 3 in word 19, and the octets read are added to word 16 unless
the tape ran out. -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-- The test's arguments: `ws`, its words, the rest of the tape and `used`. -/
def primeCallArgs : List Instr :=
  [.mov .rdi (.mem (sp 40)),
   .mov32 .rsi (.imm (BitVec.ofNat 32 (VG.Impl.Dsa.Generation.Layout.domainCheck / 8))),
   .mov .rdx (.mem (sp 104)), .alu .add .rdx (.mem (sp 128)),
   .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
   .mov .r8 (.reg .rsp), .alu .add .r8 (.imm 152)]

/-- Add the octets read to the cursor if the tape sufficed, then store the
status (returned in `eax`), with 2 as 3. -/
def primeCallResult : Prog isa :=
  .seq (.block [.mov32 .rax (.reg .rax), .alu .test .rax (.reg .rax)])
    (.seq (.ite .e (.block [])
        (.block [.mov .rcx (.mem (sp 152)), .alu .add .rcx (.mem (sp 128)), .store (sp 128) .rcx]))
      (.block [.mov .rcx (.reg .rax), .shift .shr .rcx 1, .alu .add .rax (.reg .rcx), .store (sp 152) .rax]))

/-- The test of a candidate of `bits` bits, called as `prime bits`. -/
def primeCall (prime : Nat → Prog isa) (bits : Nat) : Prog isa :=
  .seq (.block primeCallArgs) (.seq (prime bits) primeCallResult)

end VG.Impl.Dsa.X86_64.Generation
