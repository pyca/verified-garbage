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
* the stack below the stack pointer, within its `cs.sum` bytes (the stack
  `c`'s frames and calls use), in nested frames of the sizes `cs` (each
  less than a page, as `alloc` requires): the granules (16 bytes of `xmm0`,
  or the 8 bytes of `r11` at the bottom of a frame whose size is not a
  multiple of 16) at the offsets `ks` from the bottom, each frame from its
  top down. The granules are those an analysis of `c` finds may hold
  secrets (all of them, if `ks` lists them all): stack `c` itself wrote, so
  the stores touch no page `c` did not;
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

/-- `zero16` at `base + 16 * (k - 1)`, …, `base + 16`, `base`, but those
whose offset from the bottom of the wiped stack (`off` plus their offset in
the frame) is not in `ks`. -/
def stores16 (ks : List Nat) (off base : Nat) : Nat → List Instr
  | 0 => []
  | k + 1 => (if ks.contains (off + base + 16 * k) then [zero16 (base + 16 * k)] else []) ++
    stores16 ks off base k

/-- The 8-byte store at `rsp` of a chunk whose size is not a multiple of 16,
if its offset `off` from the bottom of the wiped stack is in `ks`. -/
def store8s (ks : List Nat) (off b : Nat) : List Instr :=
  if b % 16 = 8 && ks.contains off then [.store { base := .rsp } .r11] else []

/-- Zero the `b` bytes at `rsp` (offset `off` from the bottom of the wiped
stack) from the top down, in 16-byte granules (and one 8-byte one at the
bottom, if `b` is not a multiple of 16), those whose offset is in `ks`. -/
def chunkStores (ks : List Nat) (off b : Nat) : List Instr :=
  stores16 ks off (b % 16) (b / 16) ++ store8s ks off b

/-- Zero the granules `ks` of the stack below `rsp`, in nested frames of the
sizes `cs`. -/
def wipe (ks : List Nat) : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (chunkStores ks bs.sum b)) (wipe ks bs)) (.free b)

/-- Chunks of at most 4080 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 4080 then [n + 1] else 4080 :: chunksAux f (n + 1 - 4080)

def chunks (n : Nat) : List Nat := chunksAux (n / 4080 + 1) n

/-- The clearing. -/
def scrubTail (v : VecLevel) (retBits : Nat) (ks cs : List Nat) : Prog isa :=
  .seq (.block (clearVec v ++ [zeroR .r11])) (.seq (wipe ks cs) (.block (clearGpr retBits)))

/-- `c`, then the clearing. -/
def scrub (v : VecLevel) (retBits : Nat) (ks cs : List Nat) (c : Prog isa) : Prog isa :=
  .seq c (scrubTail v retBits ks cs)

end VG.Impl.Scrub.X86_64
