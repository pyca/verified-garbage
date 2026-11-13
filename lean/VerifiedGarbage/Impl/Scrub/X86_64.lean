module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Returning without secret residue (x86-64)

`scrub v retBits cs c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`X86_64.NoResidue`):

* the SSE registers, with `pxor x, x` (`v = .sse`, for code without VEX or
  EVEX instructions, which leaves their upper halves as the caller left
  them) or `vpxor x, x, x` (`v = .avx`, which also zeroes bits 511:128 of
  `zmm0`–`zmm15`); with `v = .evex`, for code that may write `zmm16`–`zmm31`
  or MXCSR, those registers too (`vpxorq z, z, z`), and MXCSR's status
  flags and reserved bits (`mxFix`), which leaves in it its control bits
  alone, those the code keeps (`abiPreserved`);
* the stack below the stack pointer, within its `cs.sum` bytes (the stack
  `c`'s frames and calls use), in nested frames of the sizes `cs` (each
  less than a page, as `alloc` requires): the granules (16 bytes of `xmm0`,
  16-byte aligned if the stack pointer is as the ABI leaves it on entry, or
  8 bytes of `r11` at the bottom or top of a frame, around them) at the
  offsets `ks` from the bottom, each frame from its top down; with `ymm0`,
  two granules at a time where they are 32-byte aligned, after a branch on
  bit 4 of the stack pointer. The granules are those an analysis of `c` finds may hold
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
  /-- As `avx`, with `vpxorq` (EVEX.512) of `zmm16`–`zmm31` and MXCSR's
  status flags cleared: for code that may write those. -/
  | evex
  deriving DecidableEq, Repr

def xregs : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def hregs : List HReg :=
  [.xmm16, .xmm17, .xmm18, .xmm19, .xmm20, .xmm21, .xmm22, .xmm23,
   .xmm24, .xmm25, .xmm26, .xmm27, .xmm28, .xmm29, .xmm30, .xmm31]

def zeroX : VecLevel → XReg → Instr
  | .sse, x => .xop (.bin .pxor x x)
  | .avx, x => .vop (.vbin .vpxor .l128 x x x)
  | .evex, x => .vop (.vbin .vpxor .l128 x x x)

/-- `vpxorq zmm, zmm, zmm`, of one of `zmm16`–`zmm31`. -/
def zeroH (h : HReg) : Instr := .e5op (.bin .vpxorq (.hi h) (.hi h) (.hi h))

/-- `zmm16`–`zmm31` zeroed, at the level `evex` alone. -/
def clearHigh : VecLevel → List Instr
  | .evex => hregs.map zeroH
  | _ => []

/-- At the level `evex`: MXCSR with its status flags (bits 5:0) and its
reserved bits (31:16, as the code that restores it clears them: see "MXCSR"
in `TCB/X86_64/Isa.lean`) cleared, through 8 bytes of a frame of 16 below
the stack pointer; `r11` is left zero, as the wipe expects it. The only way
the generated code writes MXCSR is Intel's sequence around the instructions
MCDT affects (`ci/check_mcdt.py`), so this is that sequence, around none:
`stmxcsr` saves MXCSR, whose saved value is masked; the prologue loads
`0x1FBF`; and the epilogue loads the saved value. -/
def mxFix : VecLevel → Prog isa
  | .evex => .frame (.alloc 16) (.block [.stmxcsr { base := .rsp }, .mov32 .r11 (.mem { base := .rsp }),
      .alu32 .and .r11 (.imm 0xFFC0), .store32 { base := .rsp } .r11,
      .mov32 .r11 (.imm 0x1FBF), .store32 { base := .rsp, disp := 4 } .r11,
      .ldmxcsr { base := .rsp, disp := 4 }, .lfence, .lfence, .ldmxcsr { base := .rsp },
      .alu32 .xor .r11 (.reg .r11)]) (.free 16)
  | _ => .block []

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

/-- `vmovdqu [rsp + off], ymm0`. -/
def zero32 (off : Nat) : Instr := .vmovdquStore .l256 { base := .rsp, disp := (off : Int) } .xmm0

/-- `mov [rsp + off], r11`. -/
def zero8 (off : Nat) : Instr := .store { base := .rsp, disp := (off : Int) } .r11

/-- Whether the wipe may store 32 bytes at a time, from `ymm0`: at every
level but `sse`, whose zeroing of `xmm0` (`zeroX`) zeroes `ymm0`. -/
def VecLevel.wide : VecLevel → Bool
  | .sse => false
  | _ => true

/-- `zero16` at `base + 16 * k`, unless its offset from the bottom of the
wiped stack (`off` plus its offset in the frame) is not in `ks`. -/
def store1 (ks : List Nat) (off base k : Nat) : List Instr :=
  if ks.contains (off + base + 16 * k) then [zero16 (base + 16 * k)] else []

/-- The 16-byte granules at `base + 16 * (k - 1)`, …, `base + 16`, `base`
zeroed, from the top down, but those whose offset from the bottom of the
wiped stack is not in `ks`: each with `zero16`, or, if `w`, a granule `t`
with `t + e` even and the one above it, both in `ks`, with one `zero32`
(which `e` makes 32-byte aligned). -/
def stores16 (w : Bool) (ks : List Nat) (off base e : Nat) : Nat → List Instr
  | 0 => []
  | 1 => store1 ks off base 0
  | k + 2 =>
    if w && (k + e) % 2 == 0 && ks.contains (off + base + 16 * (k + 1)) && ks.contains (off + base + 16 * k) then
      zero32 (base + 16 * k) :: stores16 w ks off base e k
    else store1 ks off base (k + 1) ++ stores16 w ks off base e (k + 1)

/-- The offset in its frame of the 16-byte granules of the chunk at offset
`off` from the bottom of the `n` bytes wiped: 8 if `n - off` is a multiple
of 16, else 0, which makes them 16-byte aligned when the stack pointer is 8
more than a multiple of 16, as on entry (the ABI's). Only speed depends on
it. -/
def phase (n off : Nat) : Nat := if (n - off) % 16 = 0 then 8 else 0

/-- Which of the 16-byte granules of the chunk at `off` start 32-byte
aligned pairs (`stores16`'s `e`), if the stack pointer is `s` modulo 32. -/
def pairPar (n s off : Nat) : Nat := (s + 31 * n + off + phase n off) % 32 / 16

/-- Zero the `b` bytes at `rsp` (offset `off` from the bottom of the `n`
wiped bytes) from the top down, those of the granules whose offset is in
`ks`: 16-byte granules at `phase n off` (`stores16`), and an 8-byte one
(`zero8`, of `r11`) below them if that is 8, and above them if they leave 8
bytes. -/
def chunkStores (w : Bool) (ks : List Nat) (n s off b : Nat) : List Instr :=
  (if (b - phase n off) % 16 = 8 && ks.contains (off + b - 8) then [zero8 (b - 8)] else []) ++
    stores16 w ks off (phase n off) (pairPar n s off) ((b - phase n off) / 16) ++
    (if phase n off = 8 && ks.contains off then [zero8 0] else [])

/-- `wipe`'s frames, for a stack pointer `s` modulo 32. -/
def wipeF (w : Bool) (ks : List Nat) (n s : Nat) : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (chunkStores w ks n s bs.sum b)) (wipeF w ks n s bs)) (.free b)

/-- Zero the granules `ks` of the stack below `rsp`, in nested frames of the
sizes `cs`. With 32-byte stores (`w`), which are faster aligned, first
`test` bit 4 of `rsp` (public), with `r11`, which is zero again after. -/
def wipe (w : Bool) (ks : List Nat) (cs : List Nat) : Prog isa :=
  if w && !ks.isEmpty then
    .seq (.block [.mov32 .r11 (.imm 16), .alu32 .test .r11 (.reg .rsp)])
      (.ite .e (.seq (.block [zeroR .r11]) (wipeF true ks cs.sum 8 cs))
        (.seq (.block [zeroR .r11]) (wipeF true ks cs.sum 24 cs)))
  else wipeF false ks cs.sum 8 cs

/-- Chunks of at most 4080 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 4080 then [n + 1] else 4080 :: chunksAux f (n + 1 - 4080)

def chunks (n : Nat) : List Nat := chunksAux (n / 4080 + 1) n

/-- The clearing: the SSE registers `xs`, at the level `evex` `zmm16`–`zmm31`
too, and the general-purpose registers
`ps` (`xmm0` and `r11`, which the wipe stores, if it stores any), at the
level `f` `evex` (by default `v`) MXCSR's status flags, the stack,
then the result's upper bits and the general-purpose registers `gs`. Code
that leaves the same MXCSR in two runs along the same path needs no `mxFix`
(`f` below `evex`), even if it writes `zmm16`–`zmm31`. -/
def scrubTail (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat)
    (f : VecLevel := v) : Prog isa :=
  .seq (.block (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR))
    (.seq (mxFix f) (.seq (wipe v.wide ks cs) (.block (retFix retBits ++ gs.map zeroR))))

/-- `c`, then the clearing. -/
def scrub (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat) (c : Prog isa)
    (f : VecLevel := v) : Prog isa :=
  .seq c (scrubTail v retBits xs ps gs ks cs f)

/-! ## What to clear

Only what `c` may have written: a register it never writes holds what it
held on entry (`Proof/Framework/X86_64/Scrub.lean`). -/

/-- Whether an instruction may write a vector register (as `KeepReg.writesVec`). -/
def writesVec : Instr → Bool
  | .movdquLoad .. | .movdquTbl .. | .xop _ | .vop _ | .vmovdquLoad .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad ..
  | .zop _
  | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpbroadcastdZ .. | .zbcstd .. | .vpmadd52Load ..
  | .eop _ | .evLoad .. | .evMadd52Load .. | .kLoad .. | .kLoad8 ..
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. => true
  | _ => false

/-- The SSE registers to clear: all of them, if `c` may write one; otherwise
`xmm0` if the wipe stores it (`ks` not empty). -/
def xsOf (c : Prog isa) (ks : List Nat) : List XReg :=
  if c.all (fun i => !writesVec i) then (if ks = [] then [] else [.xmm0]) else xregs

/-- `r11`, if the wipe stores it. -/
def psOf (ks : List Nat) : List Reg := if ks = [] then [] else [.r11]

/-- The scratch registers `c` may write (`Taint.clobbers`, as `dstOf` and
the frames' and `mul`'s registers), or `r11` alone if none, so that the last
`xor` leaves known flags. -/
def gsOf (clobbers : Instr → Reg → Bool) (c : Prog isa) : List Reg :=
  let w := scratchRegs.filter fun r => !c.all (fun i => !clobbers i r)
  if w = [] then [.r11] else w

end VG.Impl.Scrub.X86_64
