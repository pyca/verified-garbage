module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateWidth
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Search
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash

/-! # One complete native p-search attempt

The search controller supplies rdi and its seed offset. All arithmetic and
primality work is native. An undersized p sets retry status without entering
primality testing, leaving the witness cursor unchanged.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-- Select the shaped-X buffer, copy the controller's current offset, and
use the wrapped seed as the streaming hash input. -/
def pAttemptArgs : List Instr :=
  [.mov .rcx (.mem (hdr 1)), .mov .rax (.mem (sp 40)), .mov .rdx (.mem (sp 24)),
   .alu .add .rax (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped)),
   .store (sp 0) .rax, .store (sp 16) .rcx, .store (sp 216) .rdx]

def stackStatus (status : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (sp 152) .rax]

def controlBase : List Instr :=
  [.mov .rdi (.mem (sp 40)),
   .alu .add .rdi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.control))]

/-- Return the body status and restore the controller base. -/
def searchReturn : List Instr :=
  controlBase ++ [.mov .rax (.mem (sp 152)), .store (hdr 2) .rax]

/-- The width rejection path does not invoke primality or advance witnesses. -/
def pTest (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (pLen : Nat) : Prog isa :=
  .seq (.block candidateWidth)
    (.ite .b (.block (stackStatus 3))
      (.seq (checkPrime mul round (pLen / 8) VG.Impl.Dsa.Generation.Layout.p pLen pLen
        (if pLen ≤ 256 then 64 else 128)) (.block primeResult)))

/-- Construct p and the generator exponent, retaining both in byte buffers. -/
def pConstruct (G : Stream) (pLen qLen : Nat) : Prog isa :=
  let count := (8 * pLen - 1) / (8 * qLen)
  .seq (.seq (pHashes G qLen count) (pShape qLen count pLen))
    (seqs [.block workspaceBase, workspace (pLen / 8), candidateFromFrame pLen qLen])

def pAttempt (G1 G256 : Stream) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (pLen qLen : Nat) : Prog isa :=
  .seq (.block pAttemptArgs)
    (.seq (.seq (pConstruct (if qLen = 20 then G1 else G256) pLen qLen) (pTest mul round pLen))
      (.block searchReturn))

def primeSearch (G1 G256 : Stream) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (pLen qLen : Nat) : Prog isa :=
  .seq (.block controlBase)
    (pSearch (pAttempt G1 G256 mul round pLen qLen) (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))

end VG.Impl.Dsa.X86_64.Generation
