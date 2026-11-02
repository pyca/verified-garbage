module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # DSA's probable-prime test as a function of its own (x86-64)

`vg_dsa_probable_prime` runs parameter generation's test (`primeBytes`:
trial division, then the blinded Miller–Rabin loop calling the shared round)
on the candidate at its offset of the generation's scratch space, so that
every hash backend's generator calls one copy of it. Its working space is
that scratch space: the candidate, the witness buffer and the arithmetic
workspace sit at the offsets `Generation.Layout` gives them.

The candidate's size, `bits` (160 or 256 for q, 1024, 2048 or 3072 for p),
is an argument: on entry the test derives from it the arithmetic's words,
the candidate's octets and offset, the octets of each witness draw and the
number of uniform witnesses, and writes them to the arithmetic workspace's
header, from which the test reads them.

The 56-byte frame keeps the six callee-saved registers and `used`.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Rsa.X86_64.Keys

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

/-- The sizes parameter generation tests: q of 160 and 256 bits, p of 1024,
2048 and 3072 bits. -/
def sizes : List Nat := [160, 256, 1024, 2048, 3072]

/-- The test's place in the generation's scratch space. -/
def layout (bits : Nat) : Impl.Dsa.ProbablePrime.Layout where
  bits := bits
  candidate := candidate bits
  scratch := [(Generation.Layout.witness, len bits), (Generation.Layout.arithmetic, Generation.Layout.arithmeticBytes)]
  size := Generation.Layout.domainCheck

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The callee-saved registers and their slots in the frame. -/
def savedRegisters : List (Nat × Reg) :=
  [(0, .rbx), (8, .rbp), (16, .r12), (24, .r13), (32, .r14), (40, .r15)]

def saveRegisters : List Instr := savedRegisters.map fun (offset, reg) => .store (sp offset) reg

def restoreRegisters : List Instr := savedRegisters.map fun (offset, reg) => .mov reg (.mem (sp offset))

/-- Keep `used` (`r8`) in the frame, the size in `r8`, `rand` in `r9` and
the working space in `rsi`, and select the arithmetic workspace. -/
def entry : List Instr :=
  [.store (sp 48) .r8, .mov .r8 (.reg .r9), .mov .r9 (.reg .rdx), .mov .rsi (.reg .rdi),
   .alu .add .rdi (.imm (BitVec.ofNat 32 Generation.Layout.arithmetic))]

/-- `words` of the size in `r8`, into `r12`: four through 256 bits, else
`bits / 64`. -/
def sizeWords : List Instr :=
  [.mov .r12 (.reg .r8), .shift .shr .r12 6, .mov32 .rax (.imm 4), .alu .cmp .r8 (.imm 257),
   .cmov .b .r12 (.reg .rax)]

/-- The arithmetic workspace of the `r12` words: `Generation.workspace`, with
the words from `r12`. -/
def sizedWorkspace : Prog isa := seqs [
  .block [.store (hdr sW) .r12, .mov32 .rax (.imm 0), .store (hdr sMinv) .rax], .block setBases,
  .block [.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .shift .shl .rax 3,
    .store (hdr sStride) .rax]]

/-- The test's arguments in the arithmetic workspace's header, those of the
size in `r8` derived from it: `draw`, `len`, `checks` and `candidate`. -/
def args : List Instr :=
  [.mov .rax (.reg .rsi), .alu .add .rax (.imm (BitVec.ofNat 32 Generation.Layout.witness)),
   .store (hdr kOut) .rax,
   .mov .rdx (.reg .r8), .shift .shr .rdx 3, .mov .rax (.reg .rdx), .mov32 .r10 (.imm 24),
   .alu .cmp .r8 (.imm 160), .cmov .e .rax (.reg .r10), .store (hdr kLen) .rax,
   .store (hdr kUsedP) .rdx,
   .mov32 .rax (.imm 64), .mov32 .rdx (.imm 128), .alu .cmp .r8 (.imm 2049),
   .cmov .ae .rax (.reg .rdx), .store (hdr kChecks) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 Generation.Layout.p)),
   .mov32 .rdx (.imm (BitVec.ofNat 32 Generation.Layout.q)), .alu .cmp .r8 (.imm 257),
   .cmov .b .rax (.reg .rdx), .mov .rdx (.reg .rsi), .alu .add .rdx (.reg .rax),
   .store (hdr 20) .rdx,
   .store (hdr kRand) .r9, .store (hdr kRandLen) .rcx,
   .mov32 .rax (.imm 0), .store (hdr kUsed) .rax]

/-- Write the octets read to `used`, and return the status, with the test's
3 for a composite as 2. -/
def exit : List Instr :=
  [.mov .rax (.mem (hdr kUsed)), .mov .r8 (.mem (sp 48)), .store { base := .r8 } .rax,
   .mov .rax (.mem (hdr kStat)), .mov .rcx (.reg .rax), .shift .shr .rcx 1,
   .alu .sub .rax (.reg .rcx)]

/-- Everything before the test. -/
def setup : Prog isa :=
  seqs [.block saveRegisters, .block entry, .block sizeWords, sizedWorkspace, .block args]

def code (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .frame (.alloc 56)
    (.seq setup (seqs [primeBytes mul round, .block exit, .block restoreRegisters]))
    (.free 56)

end VG.Impl.Dsa.X86_64.ProbablePrime
