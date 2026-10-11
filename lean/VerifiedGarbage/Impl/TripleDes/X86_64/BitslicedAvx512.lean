module

public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocZ
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocZ

/-!
# Bitsliced Triple DES ECB on x86-64 with AVX-512

`vg_triple_des_ecb_{en,de}crypt_avx512(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

As `BitslicedAvx2`, but on 512 blocks at a time, in 512-bit words, while at
least 512 blocks are left; the blocks left after that go through the AVX2
code (`BitsliceAvx2.ecb`: a batch of 256 if that many are left, then the
SSE2 code).

* The state of 512 blocks (64 words of 64 bytes) is the 4096 bytes of the
  blocks themselves: the 64 bytes at `rsi + 64 i` hold blocks `8i … 8i + 7`,
  and each of the eight quadword lanes of the 64 words is transposed in
  place. Word `j`'s bit `64 q + i` is then bit `j` of block `8i + q`.
* The S-box circuits are fused into functions of up to three words
  (`BitsliceAllocZ`), most of them one `vpternlogd`.
* Everything the loops count is in registers, and `rbx` is saved in the
  scratch buffer, as in `BitslicedAvx2`.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64.BitsliceAvx512

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Impl.TripleDes.X86_64.Bitslice (passKey swapMask)
open VG.Spec.TripleDes (Direction)

/-- State word `j`, at `rsi + 64 j`. -/
def word (j : Nat) : MemOp := { base := .rsi, disp := ((64 * j : Nat) : Int) }

def zload (d : XReg) (m : MemOp) : Instr := .vmovdqu32Load d m
def zstore (m : MemOp) (r : XReg) : Instr := .vmovdqu32Store m r

/-- Where `rbx` is saved: the last 8 bytes of the scratch buffer. -/
def rbxSave : MemOp := { base := .rcx, disp := 1016 }

/-- The spill slots the circuits may use. -/
def spills : Nat := 8

/-! ## S-boxes -/

def inRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5]
def outRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]
def freeRegs : List XReg :=
  [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]
def inReg (i : Nat) : XReg := inRegs.getD i .xmm0
def outReg (i : Nat) : XReg := outRegs.getD i .xmm0

/-- The key bit mask. -/
def maskReg : XReg := .xmm15

/-! The code of the S-boxes, as `compile` allocates it for their circuits. It is written
out (and `#guard` checks that it is what `compile` produces) so that the kernel, which
evaluates the code in the proofs, does not have to run the allocator. -/

/-- The code of S-box 1. -/
def sboxCode0 : List Instr := [
  .zop (.zbin .vpandnq .xmm6 .xmm1 .xmm5), .zop (.zbin .vpxord .xmm7 .xmm2 .xmm6),
  .zop (.zbin .vporq .xmm8 .xmm3 .xmm0), .zop (.zbin .vpxord .xmm9 .xmm5 .xmm3),
  .zop (.zbin .vpandq .xmm10 .xmm8 .xmm9), .zop (.zbin .vpxord .xmm11 .xmm2 .xmm10),
  .zop (.zbin .vpandnq .xmm12 .xmm7 .xmm11), .zop (.zbin .vpxord .xmm13 .xmm1 .xmm0),
  .zop (.vmovdqa64 .xmm14 .xmm7), .zop (.vpternlogd .xmm14 .xmm3 .xmm13 0x90#8),
  .zop (.vpternlogd .xmm14 .xmm0 .xmm10 0x1e#8), .zop (.zbin .vpandnq .xmm10 .xmm12 .xmm14),
  .zop (.zbin .vporq .xmm0 .xmm5 .xmm0), .zop (.zbin .vporq .xmm15 .xmm14 .xmm0),
  .zop (.zbin .vpandnq .xmm11 .xmm11 .xmm1), .zop (.vpternlogd .xmm2 .xmm11 .xmm0 0x9c#8),
  .zop (.vpternlogd .xmm2 .xmm13 .xmm9 0xf4#8), .zop (.zbin .vpandnq .xmm6 .xmm6 .xmm3),
  .zop (.vpternlogd .xmm6 .xmm7 .xmm15 0x06#8), .zop (.vpternlogd .xmm14 .xmm6 .xmm8 0x93#8),
  .zop (.vmovdqa64 .xmm3 .xmm4), .zop (.vpternlogd .xmm3 .xmm15 .xmm11 0x06#8),
  .zop (.zbin .vpxord .xmm3 .xmm3 .xmm14), .zop (.vpternlogd .xmm11 .xmm13 .xmm6 0xf6#8),
  .zop (.vpternlogd .xmm5 .xmm8 .xmm11 0x96#8), .zop (.zbin .vpxord .xmm14 .xmm14 .xmm5),
  .zop (.vpternlogd .xmm12 .xmm14 .xmm4 0x36#8), .zop (.vpternlogd .xmm8 .xmm2 .xmm15 0xde#8),
  .zop (.zbin .vpxord .xmm8 .xmm5 .xmm8), .zop (.vpternlogd .xmm13 .xmm8 .xmm14 0x36#8),
  .zop (.vpternlogd .xmm13 .xmm10 .xmm4 0x1e#8), .zop (.vpternlogd .xmm8 .xmm1 .xmm7 0x0e#8),
  .zop (.vpternlogd .xmm8 .xmm10 .xmm5 0x78#8), .zop (.vpternlogd .xmm2 .xmm8 .xmm4 0x1e#8),
  .zop (.vmovdqa64 .xmm0 .xmm2), .zop (.vmovdqa64 .xmm1 .xmm3), .zop (.vmovdqa64 .xmm2 .xmm13),
  .zop (.vmovdqa64 .xmm3 .xmm12)]

/-- The code of S-box 2. -/
def sboxCode1 : List Instr := [
  .zop (.zbin .vpxord .xmm6 .xmm4 .xmm1), .zop (.vmovdqa64 .xmm7 .xmm1),
  .zop (.vpternlogd .xmm7 .xmm5 .xmm0 0xb0#8), .zop (.zbin .vporq .xmm8 .xmm4 .xmm7),
  .zop (.zbin .vpandnq .xmm9 .xmm0 .xmm6), .zop (.vpternlogd .xmm1 .xmm5 .xmm6 0x78#8),
  .zop (.zbin .vpandq .xmm10 .xmm3 .xmm0), .zop (.vpternlogd .xmm7 .xmm8 .xmm9 0x48#8),
  .zop (.zbin .vpandq .xmm11 .xmm3 .xmm7), .zop (.vpternlogd .xmm5 .xmm11 .xmm11 0xc3#8),
  .zop (.zbin .vpxord .xmm0 .xmm0 .xmm6), .zop (.zbin .vpandnq .xmm12 .xmm10 .xmm0),
  .zop (.zbin .vpxord .xmm13 .xmm5 .xmm12), .zop (.vmovdqa64 .xmm14 .xmm2),
  .zop (.vpternlogd .xmm14 .xmm7 .xmm10 0xb0#8), .zop (.zbin .vpxord .xmm14 .xmm14 .xmm13),
  .zop (.zbin .vpandnq .xmm12 .xmm12 .xmm4), .zop (.zbin .vpxord .xmm4 .xmm1 .xmm12),
  .zop (.zbin .vpxord .xmm3 .xmm3 .xmm0), .zop (.vpternlogd .xmm5 .xmm3 .xmm4 0x9c#8),
  .zop (.vmovdqa64 .xmm15 .xmm5), .zop (.vpternlogd .xmm15 .xmm8 .xmm2 0xb4#8),
  .zop (.vpternlogd .xmm3 .xmm11 .xmm12 0xf6#8), .zop (.zbin .vpxord .xmm8 .xmm8 .xmm13),
  .zop (.zbin .vporq .xmm10 .xmm10 .xmm8), .zop (.zbin .vpxord .xmm12 .xmm3 .xmm10),
  .zop (.vpternlogd .xmm5 .xmm7 .xmm13 0x96#8), .zop (.zbin .vpandq .xmm3 .xmm6 .xmm3),
  .zop (.vpternlogd .xmm3 .xmm10 .xmm5 0x78#8), .zop (.vpternlogd .xmm12 .xmm3 .xmm2 0x1e#8),
  .zop (.zbin .vporq .xmm8 .xmm0 .xmm8), .zop (.vpternlogd .xmm8 .xmm3 .xmm4 0xb4#8),
  .zop (.vpternlogd .xmm2 .xmm1 .xmm9 0xf4#8), .zop (.zbin .vpxord .xmm8 .xmm2 .xmm8),
  .zop (.vmovdqa64 .xmm0 .xmm8), .zop (.vmovdqa64 .xmm1 .xmm12), .zop (.vmovdqa64 .xmm2 .xmm14),
  .zop (.vmovdqa64 .xmm3 .xmm15)]

/-- The code of S-box 3. -/
def sboxCode2 : List Instr := [
  .zop (.zbin .vpandnq .xmm6 .xmm4 .xmm5), .zop (.zbin .vpxord .xmm7 .xmm3 .xmm0),
  .zop (.zbin .vporq .xmm8 .xmm6 .xmm7), .zop (.zbin .vpxord .xmm9 .xmm2 .xmm0),
  .zop (.zbin .vpandnq .xmm10 .xmm5 .xmm9), .zop (.zbin .vpxord .xmm11 .xmm8 .xmm10),
  .zop (.zbin .vpxord .xmm12 .xmm4 .xmm7), .zop (.vpternlogd .xmm8 .xmm12 .xmm0 0xb4#8),
  .zop (.vmovdqa64 .xmm13 .xmm2), .zop (.vpternlogd .xmm13 .xmm0 .xmm11 0xf8#8),
  .zop (.vpternlogd .xmm13 .xmm12 .xmm5 0x6c#8), .zop (.vmovdqa64 .xmm14 .xmm13),
  .zop (.vpternlogd .xmm14 .xmm11 .xmm1 0xb4#8), .zop (.zbin .vpxord .xmm15 .xmm5 .xmm2),
  .vmovdqu32Store (spillAt 0) .xmm14,
  .zop (.vmovdqa64 .xmm14 .xmm3), .zop (.vpternlogd .xmm14 .xmm8 .xmm15 0xf6#8),
  .zop (.vpternlogd .xmm14 .xmm7 .xmm9 0x70#8), .zop (.zbin .vporq .xmm15 .xmm10 .xmm15),
  .zop (.zbin .vpandq .xmm0 .xmm2 .xmm0), .zop (.zbin .vpandnq .xmm10 .xmm4 .xmm0),
  .zop (.vpternlogd .xmm10 .xmm13 .xmm15 0xb4#8), .zop (.zbin .vpandq .xmm9 .xmm8 .xmm10),
  .zop (.vpternlogd .xmm9 .xmm12 .xmm0 0x0e#8), .zop (.zbin .vpxord .xmm9 .xmm5 .xmm9),
  .zop (.vpternlogd .xmm14 .xmm9 .xmm1 0x6c#8), .zop (.vmovdqa64 .xmm5 .xmm11),
  .zop (.vpternlogd .xmm5 .xmm11 .xmm11 0x0f#8), .zop (.vpternlogd .xmm3 .xmm4 .xmm5 0xfe#8),
  .zop (.zbin .vpxord .xmm3 .xmm12 .xmm3), .zop (.vpternlogd .xmm11 .xmm1 .xmm8 0x8c#8),
  .zop (.vpternlogd .xmm11 .xmm15 .xmm3 0x96#8), .zop (.vpternlogd .xmm13 .xmm2 .xmm5 0x78#8),
  .zop (.zbin .vpxord .xmm9 .xmm6 .xmm9), .zop (.vpternlogd .xmm9 .xmm3 .xmm13 0x1e#8),
  .zop (.vpternlogd .xmm9 .xmm10 .xmm1 0x1e#8),
  .vmovdqu32Load .xmm0 (spillAt 0),
  .zop (.vmovdqa64 .xmm1 .xmm9), .zop (.vmovdqa64 .xmm2 .xmm14), .zop (.vmovdqa64 .xmm3 .xmm11)]

/-- The code of S-box 4. -/
def sboxCode3 : List Instr := [
  .zop (.zbin .vpxord .xmm5 .xmm5 .xmm3), .zop (.zbin .vpxord .xmm3 .xmm3 .xmm1),
  .zop (.vmovdqa64 .xmm6 .xmm1), .zop (.vpternlogd .xmm6 .xmm4 .xmm2 0x1e#8),
  .zop (.zbin .vpandnq .xmm6 .xmm6 .xmm3), .zop (.zbin .vpandnq .xmm7 .xmm4 .xmm3),
  .zop (.zbin .vpxord .xmm8 .xmm2 .xmm7), .zop (.vmovdqa64 .xmm9 .xmm6),
  .zop (.vpternlogd .xmm9 .xmm5 .xmm8 0x0e#8), .zop (.zbin .vpxord .xmm10 .xmm4 .xmm9),
  .zop (.zbin .vpandq .xmm8 .xmm8 .xmm10), .zop (.zbin .vpxord .xmm5 .xmm5 .xmm10),
  .zop (.vpternlogd .xmm3 .xmm5 .xmm8 0x8c#8), .zop (.zbin .vpxord .xmm3 .xmm6 .xmm3),
  .zop (.zbin .vpxord .xmm2 .xmm4 .xmm2), .zop (.vpternlogd .xmm5 .xmm1 .xmm7 0x1e#8),
  .zop (.vpternlogd .xmm9 .xmm5 .xmm2 0xb4#8), .zop (.vmovdqa64 .xmm7 .xmm9),
  .zop (.vpternlogd .xmm7 .xmm0 .xmm3 0xb4#8), .zop (.vpternlogd .xmm9 .xmm9 .xmm9 0x0f#8),
  .zop (.vmovdqa64 .xmm1 .xmm9), .zop (.vpternlogd .xmm1 .xmm3 .xmm0 0xb4#8),
  .zop (.vpternlogd .xmm2 .xmm3 .xmm9 0x06#8), .zop (.vpternlogd .xmm5 .xmm8 .xmm2 0x1e#8),
  .zop (.vmovdqa64 .xmm2 .xmm5), .zop (.vpternlogd .xmm2 .xmm10 .xmm0 0x1e#8),
  .zop (.vpternlogd .xmm5 .xmm0 .xmm10 0x78#8), .zop (.vmovdqa64 .xmm0 .xmm5),
  .vmovdqu32Store (spillAt 0) .xmm1,
  .zop (.vmovdqa64 .xmm1 .xmm2),
  .vmovdqu32Load .xmm2 (spillAt 0),
  .zop (.vmovdqa64 .xmm3 .xmm7)]

/-- The code of S-box 5. -/
def sboxCode4 : List Instr := [
  .zop (.zbin .vporq .xmm6 .xmm5 .xmm3), .zop (.zbin .vpandnq .xmm7 .xmm0 .xmm6),
  .zop (.zbin .vpxord .xmm8 .xmm5 .xmm7), .zop (.zbin .vpxord .xmm9 .xmm3 .xmm8),
  .zop (.zbin .vporq .xmm10 .xmm2 .xmm9), .zop (.vpternlogd .xmm3 .xmm7 .xmm2 0xb4#8),
  .zop (.zbin .vporq .xmm9 .xmm5 .xmm9), .zop (.vmovdqa64 .xmm7 .xmm9),
  .zop (.vpternlogd .xmm7 .xmm1 .xmm3 0x78#8), .zop (.zbin .vpxord .xmm7 .xmm2 .xmm7),
  .zop (.zbin .vpxord .xmm0 .xmm0 .xmm7), .zop (.zbin .vporq .xmm11 .xmm8 .xmm0),
  .zop (.zbin .vpandq .xmm12 .xmm1 .xmm11), .zop (.zbin .vpandq .xmm13 .xmm2 .xmm9),
  .zop (.vpternlogd .xmm13 .xmm8 .xmm12 0x96#8), .zop (.zbin .vpandnq .xmm11 .xmm5 .xmm11),
  .zop (.zbin .vpxord .xmm1 .xmm1 .xmm10), .zop (.vmovdqa64 .xmm14 .xmm1),
  .zop (.vpternlogd .xmm14 .xmm3 .xmm11 0x6f#8), .zop (.vpternlogd .xmm7 .xmm14 .xmm4 0xb4#8),
  .zop (.vpternlogd .xmm11 .xmm13 .xmm1 0xde#8), .zop (.vpternlogd .xmm11 .xmm3 .xmm12 0xb0#8),
  .zop (.vpternlogd .xmm1 .xmm0 .xmm11 0x78#8), .zop (.vpternlogd .xmm9 .xmm1 .xmm3 0xec#8),
  .zop (.vpternlogd .xmm12 .xmm4 .xmm9 0x48#8), .zop (.zbin .vpxord .xmm13 .xmm12 .xmm13),
  .zop (.vpternlogd .xmm5 .xmm11 .xmm6 0x96#8), .zop (.vpternlogd .xmm5 .xmm2 .xmm1 0x78#8),
  .zop (.vpternlogd .xmm11 .xmm4 .xmm10 0xce#8), .zop (.zbin .vpxord .xmm11 .xmm11 .xmm5),
  .zop (.vpternlogd .xmm5 .xmm10 .xmm3 0x06#8), .zop (.vpternlogd .xmm5 .xmm8 .xmm1 0x96#8),
  .zop (.vpternlogd .xmm5 .xmm10 .xmm4 0x78#8), .zop (.vmovdqa64 .xmm0 .xmm13),
  .zop (.vmovdqa64 .xmm1 .xmm7), .zop (.vmovdqa64 .xmm2 .xmm5), .zop (.vmovdqa64 .xmm3 .xmm11)]

/-- The code of S-box 6. -/
def sboxCode5 : List Instr := [
  .zop (.vmovdqa64 .xmm6 .xmm5), .zop (.vpternlogd .xmm6 .xmm4 .xmm0 0xe0#8),
  .zop (.vmovdqa64 .xmm7 .xmm6), .zop (.vpternlogd .xmm7 .xmm4 .xmm1 0x96#8),
  .zop (.zbin .vpxord .xmm8 .xmm0 .xmm7), .zop (.zbin .vpandnq .xmm9 .xmm8 .xmm1),
  .zop (.zbin .vpandq .xmm8 .xmm5 .xmm8), .zop (.zbin .vpxord .xmm10 .xmm4 .xmm8),
  .zop (.zbin .vpxord .xmm11 .xmm5 .xmm3), .zop (.zbin .vporq .xmm12 .xmm10 .xmm11),
  .zop (.zbin .vpxord .xmm13 .xmm7 .xmm12), .zop (.zbin .vpandq .xmm14 .xmm3 .xmm13),
  .zop (.zbin .vpandnq .xmm15 .xmm0 .xmm14), .zop (.zbin .vporq .xmm10 .xmm9 .xmm10),
  .vmovdqu32Store (spillAt 0) .xmm8,
  .zop (.zbin .vpxord .xmm8 .xmm15 .xmm10),
  .vmovdqu32Store (spillAt 1) .xmm7,
  .zop (.vmovdqa64 .xmm7 .xmm13), .zop (.vpternlogd .xmm7 .xmm8 .xmm2 0x78#8),
  .zop (.zbin .vpxord .xmm12 .xmm4 .xmm12), .zop (.vpternlogd .xmm3 .xmm0 .xmm12 0xb4#8),
  .vmovdqu32Store (spillAt 2) .xmm7,
  .zop (.vmovdqa64 .xmm7 .xmm3), .zop (.vpternlogd .xmm7 .xmm1 .xmm14 0xf4#8),
  .zop (.zbin .vporq .xmm11 .xmm4 .xmm11), .zop (.zbin .vporq .xmm6 .xmm6 .xmm7),
  .zop (.vpternlogd .xmm6 .xmm8 .xmm11 0x96#8), .zop (.vpternlogd .xmm10 .xmm5 .xmm13 0xe0#8),
  .zop (.zbin .vpxord .xmm10 .xmm3 .xmm10), .zop (.zbin .vpandnq .xmm15 .xmm15 .xmm10),
  .zop (.vpternlogd .xmm15 .xmm9 .xmm2 0x1e#8),
  .vmovdqu32Load .xmm9 (spillAt 1),
  .zop (.vpternlogd .xmm1 .xmm9 .xmm10 0x90#8), .zop (.vpternlogd .xmm12 .xmm11 .xmm11 0xc3#8),
  .zop (.vpternlogd .xmm1 .xmm2 .xmm12 0x12#8), .zop (.zbin .vpxord .xmm6 .xmm1 .xmm6),
  .zop (.zbin .vpxord .xmm3 .xmm5 .xmm3),
  .vmovdqu32Load .xmm5 (spillAt 0),
  .zop (.vpternlogd .xmm3 .xmm0 .xmm5 0x60#8), .zop (.vpternlogd .xmm3 .xmm14 .xmm12 0x96#8),
  .zop (.vpternlogd .xmm3 .xmm7 .xmm2 0xb4#8),
  .vmovdqu32Load .xmm0 (spillAt 2),
  .zop (.vmovdqa64 .xmm1 .xmm15), .zop (.vmovdqa64 .xmm2 .xmm6)]

/-- The code of S-box 7. -/
def sboxCode6 : List Instr := [
  .zop (.zbin .vpxord .xmm6 .xmm2 .xmm1), .zop (.zbin .vpxord .xmm7 .xmm3 .xmm6),
  .zop (.zbin .vpandq .xmm8 .xmm0 .xmm7), .zop (.zbin .vpandq .xmm9 .xmm2 .xmm6),
  .zop (.zbin .vpxord .xmm10 .xmm4 .xmm9), .zop (.zbin .vpandq .xmm11 .xmm8 .xmm10),
  .zop (.zbin .vpandq .xmm12 .xmm0 .xmm9), .zop (.zbin .vpxord .xmm13 .xmm3 .xmm12),
  .zop (.zbin .vporq .xmm14 .xmm10 .xmm13), .zop (.zbin .vpxord .xmm6 .xmm0 .xmm6),
  .zop (.zbin .vpxord .xmm15 .xmm14 .xmm6), .zop (.vpternlogd .xmm15 .xmm5 .xmm11 0xb4#8),
  .zop (.zbin .vpandnq .xmm7 .xmm7 .xmm1), .zop (.zbin .vpxord .xmm13 .xmm8 .xmm13),
  .vmovdqu32Store (spillAt 0) .xmm15,
  .zop (.vmovdqa64 .xmm15 .xmm13), .zop (.vpternlogd .xmm15 .xmm10 .xmm7 0x1e#8),
  .zop (.zbin .vpxord .xmm6 .xmm8 .xmm6), .zop (.zbin .vpandnq .xmm2 .xmm6 .xmm2),
  .zop (.zbin .vpxord .xmm13 .xmm1 .xmm13), .zop (.vpternlogd .xmm13 .xmm10 .xmm2 0xb4#8),
  .zop (.zbin .vpandnq .xmm12 .xmm12 .xmm6), .zop (.zbin .vporq .xmm2 .xmm2 .xmm12),
  .zop (.vpternlogd .xmm14 .xmm13 .xmm4 0x48#8), .zop (.zbin .vpxord .xmm14 .xmm2 .xmm14),
  .zop (.vmovdqa64 .xmm6 .xmm13), .zop (.vpternlogd .xmm6 .xmm14 .xmm5 0x78#8),
  .zop (.vpternlogd .xmm12 .xmm10 .xmm3 0xf4#8), .zop (.vpternlogd .xmm12 .xmm9 .xmm13 0xe0#8),
  .zop (.vpternlogd .xmm0 .xmm7 .xmm2 0x60#8), .zop (.zbin .vporq .xmm0 .xmm11 .xmm0),
  .zop (.zbin .vpxord .xmm11 .xmm12 .xmm0), .zop (.vmovdqa64 .xmm2 .xmm15),
  .zop (.vpternlogd .xmm2 .xmm11 .xmm5 0xb4#8), .zop (.vpternlogd .xmm15 .xmm4 .xmm0 0x87#8),
  .zop (.vpternlogd .xmm5 .xmm14 .xmm12 0xf6#8), .zop (.vpternlogd .xmm5 .xmm11 .xmm15 0x96#8),
  .vmovdqu32Load .xmm0 (spillAt 0),
  .zop (.vmovdqa64 .xmm1 .xmm6),
  .vmovdqu32Store (spillAt 1) .xmm2,
  .zop (.vmovdqa64 .xmm2 .xmm5),
  .vmovdqu32Load .xmm3 (spillAt 1)]

/-- The code of S-box 8. -/
def sboxCode7 : List Instr := [
  .zop (.zbin .vpandnq .xmm6 .xmm4 .xmm3), .zop (.vmovdqa64 .xmm7 .xmm2),
  .zop (.vpternlogd .xmm7 .xmm1 .xmm3 0xb4#8), .zop (.zbin .vpandq .xmm8 .xmm5 .xmm7),
  .zop (.zbin .vpandnq .xmm9 .xmm6 .xmm8), .zop (.zbin .vpandnq .xmm10 .xmm7 .xmm4),
  .zop (.zbin .vporq .xmm11 .xmm5 .xmm10), .zop (.vmovdqa64 .xmm12 .xmm1),
  .zop (.vpternlogd .xmm12 .xmm4 .xmm3 0xb4#8), .zop (.zbin .vpandq .xmm13 .xmm11 .xmm12),
  .zop (.zbin .vporq .xmm8 .xmm8 .xmm13), .zop (.zbin .vpandnq .xmm11 .xmm11 .xmm3),
  .zop (.vpternlogd .xmm11 .xmm13 .xmm7 0x69#8), .zop (.zbin .vpxord .xmm6 .xmm6 .xmm11),
  .zop (.vmovdqa64 .xmm7 .xmm6), .zop (.vpternlogd .xmm7 .xmm9 .xmm0 0x1e#8),
  .zop (.zbin .vpxord .xmm6 .xmm5 .xmm6), .zop (.zbin .vpxord .xmm11 .xmm4 .xmm11),
  .zop (.vmovdqa64 .xmm13 .xmm11), .zop (.vpternlogd .xmm13 .xmm1 .xmm6 0x78#8),
  .zop (.zbin .vpxord .xmm10 .xmm10 .xmm13), .zop (.vpternlogd .xmm4 .xmm8 .xmm13 0xf6#8),
  .zop (.vpternlogd .xmm4 .xmm1 .xmm6 0x96#8), .zop (.vpternlogd .xmm8 .xmm4 .xmm0 0x6c#8),
  .zop (.zbin .vpxord .xmm12 .xmm12 .xmm10), .zop (.vpternlogd .xmm11 .xmm12 .xmm2 0x36#8),
  .zop (.vpternlogd .xmm5 .xmm0 .xmm11 0x48#8), .zop (.zbin .vpxord .xmm5 .xmm5 .xmm10),
  .zop (.vpternlogd .xmm4 .xmm12 .xmm2 0x40#8), .zop (.vpternlogd .xmm4 .xmm9 .xmm11 0x96#8),
  .zop (.vpternlogd .xmm10 .xmm4 .xmm0 0x1e#8), .zop (.vmovdqa64 .xmm0 .xmm5),
  .zop (.vmovdqa64 .xmm1 .xmm8), .zop (.vmovdqa64 .xmm2 .xmm7), .zop (.vmovdqa64 .xmm3 .xmm10)]

def sboxCode : Nat → List Instr
  | 0 => sboxCode0 | 1 => sboxCode1 | 2 => sboxCode2 | 3 => sboxCode3
  | 4 => sboxCode4 | 5 => sboxCode5 | 6 => sboxCode6 | _ => sboxCode7

#guard (List.range 8).all fun j => sboxCode j ==
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills)

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx), .vop (.vmovq maskReg .rbx),
   .zop (.vpbroadcastq maskReg maskReg), zload (inReg i) (word (readWord ρ (eBit (inBit j i)))),
   zbin .vpxord (inReg i) (inReg i) maskReg]

def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [zload maskReg (word (writeWord ρ (outBit j i))), zbin .vpxord (outReg i) (outReg i) maskReg,
     zstore (word (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

def keyLoad : List Instr :=
  [.mov .rax (.mem { base := .r8, disp := 0 }), .alu .add .r8 (.reg .r9), .shift .ror .rax 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

def roundPair : List Instr := round .ba ++ round .ab ++ ([.alu .sub .r10 (.imm 1)] : List Instr)

def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [zload .xmm0 (word (lWord q)), zload .xmm1 (word (rWord q)), zstore (word (lWord q)) .xmm1,
     zstore (word (rWord q)) .xmm0]

def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [.mov .r8 (.reg .rdi), .alu .add .r8 (.imm (BitVec.ofNat 32 (passKey d p).1)),
   .mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))]

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

def bcast (d : XReg) (v : BitVec 64) : List Instr :=
  [.movImm64 .rbx v, .vop (.vmovq d .rbx), .zop (.vpbroadcastq d d)]

def swapBits (a b t m : XReg) (s : Nat) : List Instr :=
  [.zop (.vshift .vpsrlq t a (BitVec.ofNat 8 s)), zbin .vpxord t t b, zbin .vpandq t t m,
   zbin .vpxord b b t, .zop (.vshift .vpsllq t t (BitVec.ofNat 8 s)), zbin .vpxord a a t]

def groupRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]
def groupReg (k : Nat) : XReg := groupRegs.getD k .xmm0

def group (w : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => zload (groupReg k) (word (w k))) ++
  ([(4, XReg.xmm13), (2, .xmm14), (1, .xmm15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .xmm8 m (unit * d)) ++
  (List.range 8).map (fun k => zstore (word (w k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  bcast .xmm13 (swapMask (4 * unit)) ++ bcast .xmm14 (swapMask (2 * unit)) ++
  bcast .xmm15 (swapMask unit)

def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

def batch (d : Direction) : Prog isa :=
  .seq (.block (transpose ++ ([.mov .r11 (.imm 3)] : List Instr)))
    (.seq (.loop (pass d) .ne)
      (.block (transpose ++
        ([.alu .add .rsi (.imm 4096), .alu .sub .rdx (.imm 512), .alu .cmp .rdx (.imm 512)] : List Instr))))

def wide (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 512)])
    (.ite .b (.block [])
      (.seq (.block [.store rbxSave .rbx])
        (.seq (.loop (batch d) .ae)
          (.block [.mov .rbx (.mem rbxSave), .vop .vzeroupper]))))

def ecb (d : Direction) : Prog isa := .seq (wide d) (BitsliceAvx2.ecb d)

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.BitsliceAvx512
