import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Verify

/-! # PKCS #1 v1.5 verification with a precomputed public key -/

namespace VG.Impl.RsaPkcs1Sig.X86_64.Precomputed

open VG VG.X86_64 Verify

/-- Keep the original arguments for the padding check, then substitute the
precomputed modulus for the public operation's modulus arguments. -/
def pubArgs : List Instr := Verify.pubArgs ++
  [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]

/-- Check the recovered encoding even when the public operation refused the
input, then mask the result with its status. In particular, no branch depends
on the status of a call with an inconsistent precomputed modulus. Slot zero
is the completed call's first stack argument, no longer needed by padding. -/
def afterPub : Prog isa :=
  .seq (.block [.store (sp 0) .rax, .mov32 .rax (.imm 1)])
    (.seq Verify.afterPub (.block [.mov .rcx (.mem (sp 0)), .alu32 .and .rax (.reg .rcx)]))

/-- The precomputed public operation, followed by the original padding check. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) afterPub)

def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite .ne ret0 (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.X86_64.Precomputed
