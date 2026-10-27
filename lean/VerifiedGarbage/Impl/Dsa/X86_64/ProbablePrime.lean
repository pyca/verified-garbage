module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Workspace
public import VerifiedGarbage.Spec.Dsa.ProbablePrime

/-! # DSA's probable-prime test as a function of its own (x86-64)

`vg_dsa_probable_prime_{bits}` runs parameter generation's test
(`primeBytes`: trial division, then the blinded Miller–Rabin loop calling the
shared round) on the candidate at its offset of the generation's scratch
space, so that every hash backend's generator calls one copy of it. Its
working space is that scratch space: the candidate, the witness buffer and
the arithmetic workspace sit at the offsets `Generation.Layout` gives them.

The 56-byte frame keeps the six callee-saved registers and `used`; the test
itself reads its arguments from the arithmetic workspace's header.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The candidate's bytes. -/
def len (bits : Nat) : Nat := bits / 8

/-- The 64-bit words of the arithmetic: four for q, `bits / 64` for p. -/
def words (bits : Nat) : Nat := if bits ≤ 256 then 4 else bits / 64

/-- The bytes of each witness drawn from the tape. -/
def draw (bits : Nat) : Nat := if bits = 160 then 24 else bits / 8

/-- The uniform witnesses Miller–Rabin requires. -/
def checks (bits : Nat) : Nat := if bits ≤ 2048 then 64 else 128

/-- The candidate's offset: q's or p's buffer. -/
def candidate (bits : Nat) : Nat :=
  if bits ≤ 256 then Generation.Layout.q else Generation.Layout.p

/-- The test's place in the generation's scratch space. -/
def layout (bits : Nat) : Spec.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := candidate bits
  scratch := [(Generation.Layout.witness, 384), (Generation.Layout.arithmetic, Generation.Layout.arithmeticBytes)]
  size := Generation.Layout.domainCheck

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The callee-saved registers and their slots in the frame. -/
def savedRegisters : List (Nat × Reg) :=
  [(0, .rbx), (8, .rbp), (16, .r12), (24, .r13), (32, .r14), (40, .r15)]

def saveRegisters : List Instr := savedRegisters.map fun (offset, reg) => .store (sp offset) reg

def restoreRegisters : List Instr := savedRegisters.map fun (offset, reg) => .mov reg (.mem (sp offset))

/-- Keep `used` (`r8`) in the frame, `rand` in `r9` and the working space in
`rsi`, and select the arithmetic workspace. -/
def entry : List Instr :=
  [.store (sp 48) .r8, .mov .r9 (.reg .rdx), .mov .rsi (.reg .rdi),
   .alu .add .rdi (.imm (BitVec.ofNat 32 Generation.Layout.arithmetic))]

/-- The test's arguments in the arithmetic workspace's header. -/
def args (bits : Nat) : List Instr :=
  [.mov .rax (.reg .rsi), .alu .add .rax (.imm (BitVec.ofNat 32 Generation.Layout.witness)),
   .store (hdr kOut) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 (draw bits))), .store (hdr kLen) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 (len bits))), .store (hdr kUsedP) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 (checks bits))), .store (hdr kChecks) .rax,
   .mov .rax (.reg .rsi), .alu .add .rax (.imm (BitVec.ofNat 32 (candidate bits))),
   .store (hdr 20) .rax,
   .store (hdr kRand) .r9, .store (hdr kRandLen) .rcx,
   .mov32 .rax (.imm 0), .store (hdr kUsed) .rax]

/-- Write the octets read to `used`, and return the status, with the test's
3 for a composite as 2. -/
def exit : List Instr :=
  [.mov .rax (.mem (hdr kUsed)), .mov .r8 (.mem (sp 48)), .store { base := .r8 } .rax,
   .mov .rax (.mem (hdr kStat)), .mov .rcx (.reg .rax), .shift .shr .rcx 1,
   .alu .sub .rax (.reg .rcx)]

/-- Everything before the test. -/
def setup (bits : Nat) : Prog isa :=
  seqs [.block saveRegisters, .block entry, workspace (words bits), .block (args bits)]

def code (bits : Nat) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .frame (.alloc 56)
    (.seq (setup bits)
      (seqs [primeBytes mul round (len bits) (draw bits), .block exit, .block restoreRegisters]))
    (.free 56)

end VG.Impl.Dsa.X86_64.ProbablePrime
