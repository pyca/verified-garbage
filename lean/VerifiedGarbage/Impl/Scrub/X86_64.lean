module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Returning without secret residue (x86-64)

`scrub v retBits cs c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`X86_64.NoResidue`):

* the SSE registers, with `pxor x, x` (`v = .sse`, for code without VEX or
  EVEX instructions, which leaves their upper halves as the caller left
  them) or `vpxor x, x, x` (`v = .avx`, which also zeroes bits 511:128 of
  `zmm0`–`zmm15`);
* the stack below the stack pointer, `cs.sum` bytes (the stack `c`'s frames
  and calls use), in nested frames of the sizes `cs` (each less than a page,
  as `alloc` requires), each zeroed from its top down with 16-byte stores of
  `xmm0` (and one 8-byte store of `r11`, if its size is not a multiple of
  16), so that the stores never skip a guard page;
* the caller-saved general-purpose registers, with `xor r32, r32`, but the
  `retBits` low bits of `rax`, the result, whose upper bits it zeroes; the
  last `xor` leaves known flags.
-/

@[expose] public section

namespace VG.Impl.Scrub.X86_64

open VG.X86_64

/-- How the vector registers are cleared. -/
inductive VecLevel
  /-- `pxor`: for code that leaves bits 511:128 of the vector registers. -/
  | sse
  /-- `vpxor` (VEX.128): zeroes bits 511:128 of `zmm0`–`zmm15` too. -/
  | avx
  deriving DecidableEq, Repr

def xregs : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def zeroX : VecLevel → XReg → Instr
  | .sse, x => .xop (.bin .pxor x x)
  | .avx, x => .vop (.vbin .vpxor .l128 x x x)

def clearVec (v : VecLevel) : List Instr := xregs.map (zeroX v)

/-- `xor r32, r32`. -/
def zeroR (r : Reg) : Instr := .alu32 .xor r (.reg r)

/-- The caller-saved general-purpose registers but `rax`. -/
def scratchRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- Clear the bits of `rax` above a result of `retBits` bits. -/
def retFix (retBits : Nat) : List Instr :=
  if retBits = 0 then [zeroR .rax]
  else if retBits < 32 then [.alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ retBits - 1)))]
  else if retBits = 32 then [.mov32 .rax (.reg .rax)]
  else []

/-- Clear the general-purpose registers (the last instruction an `xor`, for
the flags). -/
def clearGpr (retBits : Nat) : List Instr := retFix retBits ++ scratchRegs.map zeroR

/-- `movdqu [rsp + off], xmm0`. -/
def zero16 (off : Nat) : Instr := .movdquStore { base := .rsp, disp := (off : Int) } .xmm0

/-- `zero16` at `base + 16 * (k - 1)`, …, `base + 16`, `base`. -/
def stores16 (base : Nat) : Nat → List Instr
  | 0 => []
  | k + 1 => zero16 (base + 16 * k) :: stores16 base k

/-- The 8-byte store at `rsp` of a chunk whose size is not a multiple of 16. -/
def store8s (b : Nat) : List Instr := if b % 16 = 8 then [.store { base := .rsp } .r11] else []

/-- Zero the `b` bytes at `rsp`, from the top down. -/
def chunkStores (b : Nat) : List Instr := stores16 (b % 16) (b / 16) ++ store8s b

/-- Zero the stack below `rsp` in nested frames of the sizes `cs`. -/
def wipe : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (chunkStores b)) (wipe bs)) (.free b)

/-- Chunks of at most 4080 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 4080 then [n + 1] else 4080 :: chunksAux f (n + 1 - 4080)

def chunks (n : Nat) : List Nat := chunksAux (n / 4080 + 1) n

/-- The clearing. -/
def scrubTail (v : VecLevel) (retBits : Nat) (cs : List Nat) : Prog isa :=
  .seq (.block (clearVec v ++ [zeroR .r11])) (.seq (wipe cs) (.block (clearGpr retBits)))

/-- `c`, then the clearing. -/
def scrub (v : VecLevel) (retBits : Nat) (cs : List Nat) (c : Prog isa) : Prog isa :=
  .seq c (scrubTail v retBits cs)

end VG.Impl.Scrub.X86_64
