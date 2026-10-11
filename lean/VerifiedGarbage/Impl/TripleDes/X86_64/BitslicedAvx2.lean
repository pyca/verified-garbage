module

public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocY
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocY

/-!
# Bitsliced Triple DES ECB on x86-64 with AVX2

`vg_triple_des_ecb_{en,de}crypt_avx2(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

As `Bitsliced`, but on 256 blocks at a time, in 256-bit words, while at
least 256 blocks are left; the blocks left after that go through the SSE2
code (`BitsliceSse.ecb`: a batch of 128 if that many are left, then the
64-block code).

* The state of 256 blocks (64 words of 32 bytes) is the 2048 bytes of the
  blocks themselves: the 32 bytes at `rsi + 32 i` hold blocks `4i … 4i + 3`
  as little-endian quadwords, and each quadword lane `q` of the 64 words is
  transposed in place as `Bitsliced` transposes its 64 words, with
  quadword shifts. Word `j`'s bit `64 q + i` is then bit `j` of block
  `4i + q`.
* Rounds are those of `Bitsliced`, in `ymm` registers, with the circuits'
  spills in 32-byte slots of the scratch buffer: the key bit masks come
  from `rax` through `rbx` (`add`, `sbb`), broadcast with `vmovq` and
  `vpbroadcastq`; `ymm15` holds all ones for the circuits' NOTs.
* Everything the loops count is in registers (`r8` the key pointer, `r9`
  its step, `r10` the pairs of rounds and `r11` the passes left), and
  `rbx`, the only callee-saved register used, is saved in the scratch
  buffer.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64.BitsliceAvx2

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Impl.TripleDes.X86_64.Bitslice (passKey swapMask)
open VG.Spec.TripleDes (Direction)

/-- State word `j`, at `rsi + 32 j`. -/
def word (j : Nat) : MemOp := { base := .rsi, disp := ((32 * j : Nat) : Int) }

def vload (d : XReg) (m : MemOp) : Instr := .vmovdquLoad .l256 d m
def vstore (m : MemOp) (r : XReg) : Instr := .vmovdquStore .l256 m r

/-- Where `rbx` is saved: the last 8 bytes of the scratch buffer. -/
def rbxSave : MemOp := { base := .rcx, disp := 1016 }

/-- The spill slots the circuits may use. -/
def spills : Nat := 8

/-! ## S-boxes -/

def inRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5]
def outRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]
def freeRegs : List XReg := [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14]
def inReg (i : Nat) : XReg := inRegs.getD i .xmm0
def outReg (i : Nat) : XReg := outRegs.getD i .xmm0

/-- All ones, for the circuits' NOTs. -/
def ones : XReg := .xmm15
/-- The key bit mask. -/
def maskReg : XReg := .xmm14

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .vop (.vbin .vpandn .l256 .xmm6 .xmm1 .xmm5), .vop (.vbin .vpxor .l256 .xmm7 .xmm2 .xmm6),
  .vop (.vbin .vpor .l256 .xmm8 .xmm3 .xmm0), .vop (.vbin .vpxor .l256 .xmm9 .xmm5 .xmm3),
  .vop (.vbin .vpand .l256 .xmm10 .xmm8 .xmm9), .vop (.vbin .vpxor .l256 .xmm11 .xmm2 .xmm10),
  .vop (.vbin .vpandn .l256 .xmm12 .xmm7 .xmm11), .vop (.vbin .vpxor .l256 .xmm13 .xmm1 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm3 .xmm13), .vop (.vbin .vpandn .l256 .xmm14 .xmm14 .xmm7),
  .vop (.vbin .vpor .l256 .xmm10 .xmm0 .xmm10), .vop (.vbin .vpxor .l256 .xmm10 .xmm14 .xmm10),
  .vop (.vbin .vpandn .l256 .xmm14 .xmm12 .xmm10), .vop (.vbin .vpor .l256 .xmm0 .xmm5 .xmm0),
  .vmovdquStore .l256 (spillAt 0) .xmm14,
  .vop (.vbin .vpor .l256 .xmm14 .xmm10 .xmm0), .vop (.vbin .vpandn .l256 .xmm11 .xmm11 .xmm1),
  .vmovdquStore .l256 (spillAt 1) .xmm1,
  .vop (.vbin .vpxor .l256 .xmm1 .xmm14 .xmm11), .vop (.vbin .vpandn .l256 .xmm0 .xmm0 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm0 .xmm11 .xmm0), .vop (.vbin .vpandn .l256 .xmm9 .xmm9 .xmm13),
  .vop (.vbin .vpor .l256 .xmm9 .xmm0 .xmm9), .vop (.vbin .vpandn .l256 .xmm6 .xmm6 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm3 .xmm7 .xmm14), .vop (.vbin .vpandn .l256 .xmm6 .xmm6 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm3 .xmm6 .xmm15), .vop (.vbin .vpand .l256 .xmm10 .xmm8 .xmm10),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm3 .xmm10), .vop (.vbin .vpandn .l256 .xmm1 .xmm4 .xmm1),
  .vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm10), .vop (.vbin .vpxor .l256 .xmm6 .xmm13 .xmm6),
  .vop (.vbin .vpor .l256 .xmm6 .xmm11 .xmm6), .vop (.vbin .vpxor .l256 .xmm6 .xmm8 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm6 .xmm5 .xmm6), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm6),
  .vop (.vbin .vpor .l256 .xmm12 .xmm12 .xmm4), .vop (.vbin .vpxor .l256 .xmm12 .xmm12 .xmm10),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm8 .xmm14), .vop (.vbin .vpor .l256 .xmm14 .xmm9 .xmm14),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm6 .xmm14), .vop (.vbin .vpor .l256 .xmm10 .xmm13 .xmm10),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm14 .xmm10),
  .vmovdquLoad .l256 .xmm13 (spillAt 0),
  .vop (.vbin .vpor .l256 .xmm8 .xmm13 .xmm4), .vop (.vbin .vpxor .l256 .xmm10 .xmm8 .xmm10),
  .vmovdquLoad .l256 .xmm8 (spillAt 1),
  .vop (.vbin .vpor .l256 .xmm7 .xmm8 .xmm7), .vop (.vbin .vpandn .l256 .xmm14 .xmm14 .xmm7),
  .vop (.vbin .vpand .l256 .xmm6 .xmm13 .xmm6), .vop (.vbin .vpxor .l256 .xmm6 .xmm14 .xmm6),
  .vop (.vbin .vpor .l256 .xmm4 .xmm6 .xmm4), .vop (.vbin .vpxor .l256 .xmm9 .xmm4 .xmm9),
  .vop (.vmovdqa .l256 .xmm0 .xmm9), .vop (.vmovdqa .l256 .xmm2 .xmm10),
  .vop (.vmovdqa .l256 .xmm3 .xmm12)]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .vop (.vbin .vpxor .l256 .xmm6 .xmm4 .xmm1), .vop (.vbin .vpandn .l256 .xmm7 .xmm0 .xmm5),
  .vop (.vbin .vpandn .l256 .xmm7 .xmm7 .xmm1), .vop (.vbin .vpor .l256 .xmm8 .xmm4 .xmm7),
  .vop (.vbin .vpandn .l256 .xmm9 .xmm0 .xmm6), .vop (.vbin .vpand .l256 .xmm10 .xmm5 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm1 .xmm10), .vop (.vbin .vpandn .l256 .xmm1 .xmm9 .xmm10),
  .vop (.vbin .vpand .l256 .xmm11 .xmm3 .xmm0), .vop (.vbin .vpxor .l256 .xmm9 .xmm7 .xmm9),
  .vop (.vbin .vpand .l256 .xmm9 .xmm8 .xmm9), .vop (.vbin .vpandn .l256 .xmm7 .xmm11 .xmm9),
  .vop (.vbin .vpand .l256 .xmm12 .xmm3 .xmm9), .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm15),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm12 .xmm5), .vop (.vbin .vpxor .l256 .xmm0 .xmm0 .xmm6),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm11 .xmm0), .vop (.vbin .vpxor .l256 .xmm14 .xmm5 .xmm13),
  .vop (.vbin .vpandn .l256 .xmm7 .xmm7 .xmm2), .vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm14),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm13 .xmm4), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm13),
  .vop (.vbin .vpandn .l256 .xmm5 .xmm10 .xmm5), .vop (.vbin .vpxor .l256 .xmm3 .xmm3 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm3), .vop (.vbin .vpandn .l256 .xmm4 .xmm2 .xmm8),
  .vop (.vbin .vpxor .l256 .xmm4 .xmm4 .xmm5), .vop (.vbin .vpxor .l256 .xmm13 .xmm12 .xmm13),
  .vop (.vbin .vpor .l256 .xmm13 .xmm3 .xmm13), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm14),
  .vop (.vbin .vpor .l256 .xmm11 .xmm11 .xmm8), .vop (.vbin .vpxor .l256 .xmm3 .xmm13 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm9 .xmm14), .vop (.vbin .vpxor .l256 .xmm14 .xmm5 .xmm14),
  .vop (.vbin .vpand .l256 .xmm14 .xmm11 .xmm14), .vop (.vbin .vpand .l256 .xmm13 .xmm6 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpor .l256 .xmm14 .xmm13 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm3 .xmm14 .xmm3), .vop (.vbin .vpandn .l256 .xmm10 .xmm10 .xmm13),
  .vop (.vbin .vpor .l256 .xmm8 .xmm0 .xmm8), .vop (.vbin .vpxor .l256 .xmm8 .xmm10 .xmm8),
  .vop (.vbin .vpor .l256 .xmm2 .xmm1 .xmm2), .vop (.vbin .vpxor .l256 .xmm8 .xmm2 .xmm8),
  .vop (.vmovdqa .l256 .xmm0 .xmm8), .vop (.vmovdqa .l256 .xmm1 .xmm3),
  .vop (.vmovdqa .l256 .xmm2 .xmm7), .vop (.vmovdqa .l256 .xmm3 .xmm4)]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .vop (.vbin .vpandn .l256 .xmm6 .xmm4 .xmm5), .vop (.vbin .vpxor .l256 .xmm7 .xmm3 .xmm0),
  .vop (.vbin .vpor .l256 .xmm8 .xmm6 .xmm7), .vop (.vbin .vpxor .l256 .xmm9 .xmm2 .xmm0),
  .vop (.vbin .vpandn .l256 .xmm10 .xmm5 .xmm9), .vop (.vbin .vpxor .l256 .xmm11 .xmm8 .xmm10),
  .vop (.vbin .vpxor .l256 .xmm12 .xmm4 .xmm7), .vop (.vbin .vpandn .l256 .xmm13 .xmm0 .xmm12),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm8 .xmm13), .vop (.vbin .vpandn .l256 .xmm8 .xmm13 .xmm11),
  .vop (.vbin .vpand .l256 .xmm14 .xmm0 .xmm11), .vop (.vbin .vpor .l256 .xmm14 .xmm2 .xmm14),
  .vop (.vbin .vpand .l256 .xmm14 .xmm5 .xmm14), .vop (.vbin .vpxor .l256 .xmm14 .xmm12 .xmm14),
  .vmovdquStore .l256 (spillAt 0) .xmm6,
  .vop (.vbin .vpandn .l256 .xmm6 .xmm1 .xmm11), .vop (.vbin .vpxor .l256 .xmm6 .xmm6 .xmm14),
  .vop (.vbin .vpand .l256 .xmm9 .xmm7 .xmm9), .vop (.vbin .vpxor .l256 .xmm7 .xmm5 .xmm2),
  .vmovdquStore .l256 (spillAt 1) .xmm6,
  .vop (.vbin .vpxor .l256 .xmm6 .xmm13 .xmm7), .vop (.vbin .vpor .l256 .xmm6 .xmm3 .xmm6),
  .vop (.vbin .vpandn .l256 .xmm9 .xmm9 .xmm6), .vop (.vbin .vpor .l256 .xmm7 .xmm10 .xmm7),
  .vop (.vbin .vpandn .l256 .xmm10 .xmm7 .xmm14), .vop (.vbin .vpand .l256 .xmm0 .xmm2 .xmm0),
  .vop (.vbin .vpandn .l256 .xmm6 .xmm4 .xmm0), .vop (.vbin .vpxor .l256 .xmm6 .xmm10 .xmm6),
  .vop (.vbin .vpand .l256 .xmm13 .xmm13 .xmm6), .vop (.vbin .vpor .l256 .xmm0 .xmm12 .xmm0),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm13 .xmm0), .vop (.vbin .vpxor .l256 .xmm13 .xmm5 .xmm13),
  .vop (.vbin .vpand .l256 .xmm9 .xmm9 .xmm1), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm11 .xmm15), .vop (.vbin .vpor .l256 .xmm4 .xmm4 .xmm11),
  .vop (.vbin .vpor .l256 .xmm4 .xmm3 .xmm4), .vop (.vbin .vpxor .l256 .xmm4 .xmm12 .xmm4),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm4), .vop (.vbin .vpandn .l256 .xmm8 .xmm8 .xmm1),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm8 .xmm7), .vop (.vbin .vpand .l256 .xmm11 .xmm2 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm14 .xmm11), .vop (.vbin .vpor .l256 .xmm11 .xmm4 .xmm11),
  .vmovdquLoad .l256 .xmm4 (spillAt 0),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm4 .xmm13), .vop (.vbin .vpxor .l256 .xmm13 .xmm11 .xmm13),
  .vop (.vbin .vpor .l256 .xmm1 .xmm6 .xmm1), .vop (.vbin .vpxor .l256 .xmm13 .xmm1 .xmm13),
  .vmovdquLoad .l256 .xmm0 (spillAt 1),
  .vop (.vmovdqa .l256 .xmm1 .xmm13), .vop (.vmovdqa .l256 .xmm2 .xmm9),
  .vop (.vmovdqa .l256 .xmm3 .xmm7)]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm3), .vop (.vbin .vpxor .l256 .xmm3 .xmm3 .xmm1),
  .vop (.vbin .vpor .l256 .xmm6 .xmm4 .xmm2), .vop (.vbin .vpxor .l256 .xmm6 .xmm1 .xmm6),
  .vop (.vbin .vpandn .l256 .xmm6 .xmm6 .xmm3), .vop (.vbin .vpandn .l256 .xmm7 .xmm4 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm8 .xmm2 .xmm7), .vop (.vbin .vpor .l256 .xmm9 .xmm5 .xmm8),
  .vop (.vbin .vpandn .l256 .xmm9 .xmm6 .xmm9), .vop (.vbin .vpxor .l256 .xmm10 .xmm4 .xmm9),
  .vop (.vbin .vpand .l256 .xmm8 .xmm8 .xmm10), .vop (.vbin .vpandn .l256 .xmm3 .xmm8 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm10), .vop (.vbin .vpandn .l256 .xmm3 .xmm3 .xmm5),
  .vop (.vbin .vpxor .l256 .xmm3 .xmm6 .xmm3), .vop (.vbin .vpxor .l256 .xmm2 .xmm4 .xmm2),
  .vop (.vbin .vpor .l256 .xmm7 .xmm1 .xmm7), .vop (.vbin .vpxor .l256 .xmm7 .xmm5 .xmm7),
  .vop (.vbin .vpandn .l256 .xmm5 .xmm2 .xmm7), .vop (.vbin .vpxor .l256 .xmm5 .xmm9 .xmm5),
  .vop (.vbin .vpandn .l256 .xmm9 .xmm3 .xmm0), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm5),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm15), .vop (.vbin .vpandn .l256 .xmm1 .xmm0 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm5), .vop (.vbin .vpxor .l256 .xmm5 .xmm3 .xmm5),
  .vop (.vbin .vpandn .l256 .xmm2 .xmm2 .xmm5), .vop (.vbin .vpor .l256 .xmm2 .xmm8 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm2 .xmm7 .xmm2), .vop (.vbin .vpor .l256 .xmm7 .xmm10 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2), .vop (.vbin .vpand .l256 .xmm10 .xmm0 .xmm10),
  .vop (.vbin .vpxor .l256 .xmm2 .xmm10 .xmm2), .vop (.vmovdqa .l256 .xmm0 .xmm2),
  .vmovdquStore .l256 (spillAt 0) .xmm1,
  .vop (.vmovdqa .l256 .xmm1 .xmm7),
  .vmovdquLoad .l256 .xmm2 (spillAt 0),
  .vop (.vmovdqa .l256 .xmm3 .xmm9)]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .vop (.vbin .vpor .l256 .xmm6 .xmm5 .xmm3), .vop (.vbin .vpandn .l256 .xmm7 .xmm0 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm8 .xmm5 .xmm7), .vop (.vbin .vpxor .l256 .xmm9 .xmm3 .xmm8),
  .vop (.vbin .vpor .l256 .xmm10 .xmm2 .xmm9), .vop (.vbin .vpandn .l256 .xmm7 .xmm2 .xmm7),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm3 .xmm7), .vop (.vbin .vpand .l256 .xmm3 .xmm1 .xmm7),
  .vop (.vbin .vpor .l256 .xmm9 .xmm5 .xmm9), .vop (.vbin .vpxor .l256 .xmm3 .xmm3 .xmm9),
  .vop (.vbin .vpxor .l256 .xmm3 .xmm2 .xmm3), .vop (.vbin .vpxor .l256 .xmm0 .xmm0 .xmm3),
  .vop (.vbin .vpor .l256 .xmm11 .xmm8 .xmm0), .vop (.vbin .vpand .l256 .xmm12 .xmm1 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm8 .xmm12), .vop (.vbin .vpand .l256 .xmm14 .xmm2 .xmm9),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm13 .xmm14), .vop (.vbin .vpandn .l256 .xmm11 .xmm5 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm7 .xmm11), .vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm10),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm13 .xmm1), .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm15),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm4 .xmm13), .vop (.vbin .vpxor .l256 .xmm3 .xmm13 .xmm3),
  .vop (.vbin .vpandn .l256 .xmm13 .xmm12 .xmm7), .vop (.vbin .vpxor .l256 .xmm11 .xmm11 .xmm1),
  .vop (.vbin .vpor .l256 .xmm11 .xmm14 .xmm11), .vop (.vbin .vpandn .l256 .xmm13 .xmm13 .xmm11),
  .vop (.vbin .vpandn .l256 .xmm11 .xmm13 .xmm10), .vop (.vbin .vpand .l256 .xmm0 .xmm0 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm0 .xmm1 .xmm0), .vop (.vbin .vpand .l256 .xmm9 .xmm7 .xmm9),
  .vop (.vbin .vpor .l256 .xmm9 .xmm0 .xmm9), .vop (.vbin .vpxor .l256 .xmm9 .xmm12 .xmm9),
  .vop (.vbin .vpand .l256 .xmm9 .xmm9 .xmm4), .vop (.vbin .vpxor .l256 .xmm14 .xmm9 .xmm14),
  .vop (.vbin .vpxor .l256 .xmm6 .xmm5 .xmm6), .vop (.vbin .vpxor .l256 .xmm6 .xmm13 .xmm6),
  .vop (.vbin .vpand .l256 .xmm2 .xmm2 .xmm0), .vop (.vbin .vpxor .l256 .xmm2 .xmm6 .xmm2),
  .vop (.vbin .vpor .l256 .xmm11 .xmm11 .xmm4), .vop (.vbin .vpxor .l256 .xmm11 .xmm11 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm10 .xmm7), .vop (.vbin .vpandn .l256 .xmm2 .xmm2 .xmm7),
  .vop (.vbin .vpxor .l256 .xmm0 .xmm8 .xmm0), .vop (.vbin .vpxor .l256 .xmm0 .xmm2 .xmm0),
  .vop (.vbin .vpand .l256 .xmm4 .xmm10 .xmm4), .vop (.vbin .vpxor .l256 .xmm0 .xmm4 .xmm0),
  .vmovdquStore .l256 (spillAt 0) .xmm0,
  .vop (.vmovdqa .l256 .xmm0 .xmm14), .vop (.vmovdqa .l256 .xmm1 .xmm3),
  .vmovdquLoad .l256 .xmm2 (spillAt 0),
  .vop (.vmovdqa .l256 .xmm3 .xmm11)]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .vop (.vbin .vpxor .l256 .xmm6 .xmm4 .xmm1), .vop (.vbin .vpor .l256 .xmm7 .xmm4 .xmm0),
  .vop (.vbin .vpand .l256 .xmm7 .xmm5 .xmm7), .vop (.vbin .vpxor .l256 .xmm6 .xmm6 .xmm7),
  .vop (.vbin .vpxor .l256 .xmm8 .xmm0 .xmm6), .vop (.vbin .vpandn .l256 .xmm9 .xmm8 .xmm1),
  .vop (.vbin .vpand .l256 .xmm8 .xmm5 .xmm8), .vop (.vbin .vpxor .l256 .xmm10 .xmm4 .xmm8),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm5 .xmm3), .vop (.vbin .vpor .l256 .xmm12 .xmm10 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm6 .xmm12), .vop (.vbin .vpand .l256 .xmm14 .xmm3 .xmm13),
  .vmovdquStore .l256 (spillAt 0) .xmm8,
  .vop (.vbin .vpandn .l256 .xmm8 .xmm0 .xmm14), .vop (.vbin .vpor .l256 .xmm10 .xmm9 .xmm10),
  .vmovdquStore .l256 (spillAt 1) .xmm6,
  .vop (.vbin .vpxor .l256 .xmm6 .xmm8 .xmm10),
  .vmovdquStore .l256 (spillAt 2) .xmm9,
  .vop (.vbin .vpand .l256 .xmm9 .xmm6 .xmm2), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm12 .xmm4 .xmm12),
  .vmovdquStore .l256 (spillAt 3) .xmm9,
  .vop (.vbin .vpandn .l256 .xmm9 .xmm12 .xmm0), .vop (.vbin .vpxor .l256 .xmm9 .xmm3 .xmm9),
  .vop (.vbin .vpandn .l256 .xmm3 .xmm14 .xmm1), .vop (.vbin .vpor .l256 .xmm3 .xmm9 .xmm3),
  .vop (.vbin .vpor .l256 .xmm11 .xmm4 .xmm11), .vop (.vbin .vpxor .l256 .xmm6 .xmm6 .xmm11),
  .vop (.vbin .vpor .l256 .xmm7 .xmm7 .xmm3), .vop (.vbin .vpxor .l256 .xmm7 .xmm6 .xmm7),
  .vop (.vbin .vpor .l256 .xmm13 .xmm5 .xmm13), .vop (.vbin .vpand .l256 .xmm13 .xmm10 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm9 .xmm13), .vop (.vbin .vpandn .l256 .xmm8 .xmm8 .xmm13),
  .vmovdquLoad .l256 .xmm10 (spillAt 2),
  .vop (.vbin .vpor .l256 .xmm10 .xmm10 .xmm2), .vop (.vbin .vpxor .l256 .xmm8 .xmm10 .xmm8),
  .vmovdquLoad .l256 .xmm10 (spillAt 1),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm10 .xmm13), .vop (.vbin .vpandn .l256 .xmm13 .xmm13 .xmm1),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm11 .xmm15), .vop (.vbin .vpxor .l256 .xmm11 .xmm12 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm11), .vop (.vbin .vpandn .l256 .xmm13 .xmm2 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm13 .xmm7),
  .vmovdquLoad .l256 .xmm13 (spillAt 0),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm0 .xmm13), .vop (.vbin .vpxor .l256 .xmm9 .xmm5 .xmm9),
  .vop (.vbin .vpand .l256 .xmm9 .xmm13 .xmm9), .vop (.vbin .vpxor .l256 .xmm11 .xmm14 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm9 .xmm11), .vop (.vbin .vpandn .l256 .xmm2 .xmm2 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm2 .xmm11),
  .vmovdquLoad .l256 .xmm0 (spillAt 3),
  .vop (.vmovdqa .l256 .xmm1 .xmm8), .vop (.vmovdqa .l256 .xmm2 .xmm7),
  .vop (.vmovdqa .l256 .xmm3 .xmm11)]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .vop (.vbin .vpxor .l256 .xmm6 .xmm2 .xmm1), .vop (.vbin .vpxor .l256 .xmm7 .xmm3 .xmm6),
  .vop (.vbin .vpand .l256 .xmm8 .xmm0 .xmm7), .vop (.vbin .vpand .l256 .xmm9 .xmm2 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm4 .xmm9), .vop (.vbin .vpand .l256 .xmm11 .xmm8 .xmm10),
  .vop (.vbin .vpand .l256 .xmm12 .xmm0 .xmm9), .vop (.vbin .vpxor .l256 .xmm13 .xmm3 .xmm12),
  .vop (.vbin .vpor .l256 .xmm14 .xmm10 .xmm13), .vop (.vbin .vpxor .l256 .xmm6 .xmm0 .xmm6),
  .vmovdquStore .l256 (spillAt 0) .xmm0,
  .vop (.vbin .vpxor .l256 .xmm0 .xmm14 .xmm6),
  .vmovdquStore .l256 (spillAt 1) .xmm9,
  .vop (.vbin .vpandn .l256 .xmm9 .xmm11 .xmm5), .vop (.vbin .vpxor .l256 .xmm0 .xmm9 .xmm0),
  .vop (.vbin .vpandn .l256 .xmm7 .xmm7 .xmm1), .vop (.vbin .vpor .l256 .xmm9 .xmm10 .xmm7),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm8 .xmm13), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm6 .xmm8 .xmm6), .vop (.vbin .vpandn .l256 .xmm2 .xmm6 .xmm2),
  .vop (.vbin .vpandn .l256 .xmm8 .xmm2 .xmm10), .vop (.vbin .vpxor .l256 .xmm13 .xmm1 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm8 .xmm13), .vop (.vbin .vpandn .l256 .xmm12 .xmm12 .xmm6),
  .vop (.vbin .vpor .l256 .xmm2 .xmm2 .xmm12), .vop (.vbin .vpxor .l256 .xmm14 .xmm4 .xmm14),
  .vop (.vbin .vpand .l256 .xmm14 .xmm13 .xmm14), .vop (.vbin .vpxor .l256 .xmm14 .xmm2 .xmm14),
  .vop (.vbin .vpand .l256 .xmm6 .xmm14 .xmm5), .vop (.vbin .vpxor .l256 .xmm6 .xmm6 .xmm13),
  .vop (.vbin .vpandn .l256 .xmm3 .xmm3 .xmm10), .vop (.vbin .vpor .l256 .xmm3 .xmm12 .xmm3),
  .vmovdquLoad .l256 .xmm12 (spillAt 1),
  .vop (.vbin .vpor .l256 .xmm13 .xmm12 .xmm13), .vop (.vbin .vpand .l256 .xmm13 .xmm3 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm14 .xmm14 .xmm13), .vop (.vbin .vpxor .l256 .xmm2 .xmm7 .xmm2),
  .vmovdquLoad .l256 .xmm7 (spillAt 0),
  .vop (.vbin .vpand .l256 .xmm2 .xmm7 .xmm2), .vop (.vbin .vpor .l256 .xmm2 .xmm11 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm2), .vop (.vbin .vpandn .l256 .xmm11 .xmm5 .xmm13),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm11 .xmm9), .vop (.vbin .vpand .l256 .xmm2 .xmm4 .xmm2),
  .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm15), .vop (.vbin .vpxor .l256 .xmm9 .xmm2 .xmm9),
  .vop (.vbin .vpxor .l256 .xmm9 .xmm13 .xmm9), .vop (.vbin .vpor .l256 .xmm5 .xmm14 .xmm5),
  .vop (.vbin .vpxor .l256 .xmm9 .xmm5 .xmm9), .vop (.vmovdqa .l256 .xmm1 .xmm6),
  .vop (.vmovdqa .l256 .xmm2 .xmm9), .vop (.vmovdqa .l256 .xmm3 .xmm11)]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .vop (.vbin .vpandn .l256 .xmm6 .xmm4 .xmm3), .vop (.vbin .vpandn .l256 .xmm7 .xmm3 .xmm1),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm2 .xmm7), .vop (.vbin .vpand .l256 .xmm8 .xmm5 .xmm7),
  .vop (.vbin .vpandn .l256 .xmm9 .xmm6 .xmm8), .vop (.vbin .vpandn .l256 .xmm10 .xmm7 .xmm4),
  .vop (.vbin .vpor .l256 .xmm11 .xmm5 .xmm10), .vop (.vbin .vpandn .l256 .xmm12 .xmm3 .xmm4),
  .vop (.vbin .vpxor .l256 .xmm12 .xmm1 .xmm12), .vop (.vbin .vpand .l256 .xmm13 .xmm11 .xmm12),
  .vop (.vbin .vpor .l256 .xmm8 .xmm8 .xmm13), .vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm15),
  .vop (.vbin .vpxor .l256 .xmm7 .xmm13 .xmm7), .vop (.vbin .vpandn .l256 .xmm11 .xmm11 .xmm3),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm7 .xmm11), .vop (.vbin .vpxor .l256 .xmm6 .xmm6 .xmm11),
  .vop (.vbin .vpor .l256 .xmm7 .xmm9 .xmm0), .vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm6 .xmm5 .xmm6), .vop (.vbin .vpand .l256 .xmm3 .xmm1 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm4 .xmm11), .vop (.vbin .vpxor .l256 .xmm3 .xmm3 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm3), .vop (.vbin .vpxor .l256 .xmm3 .xmm8 .xmm3),
  .vop (.vbin .vpor .l256 .xmm3 .xmm4 .xmm3), .vop (.vbin .vpxor .l256 .xmm6 .xmm1 .xmm6),
  .vop (.vbin .vpxor .l256 .xmm6 .xmm3 .xmm6), .vop (.vbin .vpand .l256 .xmm8 .xmm8 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm6), .vop (.vbin .vpxor .l256 .xmm12 .xmm12 .xmm10),
  .vop (.vbin .vpor .l256 .xmm11 .xmm2 .xmm11), .vop (.vbin .vpxor .l256 .xmm11 .xmm12 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm11), .vop (.vbin .vpand .l256 .xmm5 .xmm5 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm5 .xmm5 .xmm10), .vop (.vbin .vpandn .l256 .xmm2 .xmm2 .xmm12),
  .vop (.vbin .vpand .l256 .xmm2 .xmm6 .xmm2), .vop (.vbin .vpxor .l256 .xmm11 .xmm9 .xmm11),
  .vop (.vbin .vpxor .l256 .xmm11 .xmm2 .xmm11), .vop (.vbin .vpor .l256 .xmm0 .xmm11 .xmm0),
  .vop (.vbin .vpxor .l256 .xmm10 .xmm0 .xmm10), .vop (.vmovdqa .l256 .xmm0 .xmm5),
  .vop (.vmovdqa .l256 .xmm1 .xmm8), .vop (.vmovdqa .l256 .xmm2 .xmm7),
  .vop (.vmovdqa .l256 .xmm3 .xmm10)]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun j => sboxCode j ==
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills) ones

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx), .vop (.vmovq maskReg .rbx),
   .vop (.vpbroadcastq .l256 maskReg maskReg), vload (inReg i) (word (readWord ρ (eBit (inBit j i)))),
   vbin .vpxor (inReg i) (inReg i) maskReg]

/-- S-box `j`'s inputs, from the most significant (whose key bit is next). -/
def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [vload maskReg (word (writeWord ρ (outBit j i))), vbin .vpxor (outReg i) (outReg i) maskReg,
     vstore (word (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

/-- Load the round key into `rax`, its bit 47 at the top, and advance the
key pointer. -/
def keyLoad : List Instr :=
  [.mov .rax (.mem { base := .r8, disp := 0 }), .alu .add .r8 (.reg .r9), .shift .ror .rax 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair : List Instr := round .ba ++ round .ab ++ ([.alu .sub .r10 (.imm 1)] : List Instr)

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [vload .xmm0 (word (lWord q)), vload .xmm1 (word (rWord q)), vstore (word (lWord q)) .xmm1,
     vstore (word (rWord q)) .xmm0]

/-- Point at the pass's first key, with its step. -/
def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [.mov .r8 (.reg .rdi), .alu .add .r8 (.imm (BitVec.ofNat 32 (passKey d p).1)),
   .mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))]

/-- Choose the pass's first key and step by the pass count, and count 8 pairs. -/
def passStart (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .r11 (.imm 3)])
    (.seq (.ite .e (.block (passKeyCode d 3))
      (.seq (.block [.alu .cmp .r11 (.imm 2)])
        (.ite .e (.block (passKeyCode d 2)) (.block (passKeyCode d 1)))))
    (.block [.mov .r10 (.imm 8)]))

def pass (d : Direction) : Prog isa :=
  .seq (passStart d) (.seq (.loop (.block roundPair) .ne)
    (.block (swapHalves ++ ([.alu .sub .r11 (.imm 1)] : List Instr))))

/-! ## Transposition -/

/-- Broadcast a 64-bit constant to every quadword of `d`. -/
def bcast (d : XReg) (v : BitVec 64) : List Instr :=
  [.movImm64 .rbx v, .vop (.vmovq d .rbx), .vop (.vpbroadcastq .l256 d d)]

/-- Exchange the bits `p + s` of `a` and `p` of `b` in every quadword lane
(`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : XReg) (s : Nat) : List Instr :=
  [.vop (.vshift .psrlq .l256 t a (BitVec.ofNat 8 s)), vbin .vpxor t t b, vbin .vpand t t m,
   vbin .vpxor b b t, .vop (.vshift .psllq .l256 t t (BitVec.ofNat 8 s)), vbin .vpxor a a t]

def groupRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]
def groupReg (k : Nat) : XReg := groupRegs.getD k .xmm0

/-- Three stages on eight words, the state words `w k`: the stage of shift
`unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1. -/
def group (w : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => vload (groupReg k) (word (w k))) ++
  ([(4, XReg.xmm13), (2, .xmm14), (1, .xmm15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .xmm8 m (unit * d)) ++
  (List.range 8).map (fun k => vstore (word (w k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  bcast .xmm13 (swapMask (4 * unit)) ++ bcast .xmm14 (swapMask (2 * unit)) ++
  bcast .xmm15 (swapMask unit)

/-- Transpose each quadword lane of the 64 state words in place: stages
32, 16, 8, then 4, 2, 1. -/
def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

/-- Three passes on 256 blocks, then the next 256. -/
def batch (d : Direction) : Prog isa :=
  .seq (.block (transpose ++ bcast ones (BitVec.allOnes 64) ++ ([.mov .r11 (.imm 3)] : List Instr)))
    (.seq (.loop (pass d) .ne)
      (.block (transpose ++
        ([.alu .add .rsi (.imm 2048), .alu .sub .rdx (.imm 256), .alu .cmp .rdx (.imm 256)] : List Instr))))

/-- Batches of 256 blocks while there are that many. -/
def wide (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 256)])
    (.ite .b (.block [])
      (.seq (.block [.store rbxSave .rbx])
        (.seq (.loop (batch d) .ae)
          (.block [.mov .rbx (.mem rbxSave), .vop .vzeroupper]))))

def ecb (d : Direction) : Prog isa := .seq (wide d) (BitsliceSse.ecb d)

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.BitsliceAvx2
