module

public import VerifiedGarbage.Impl.AesXts.X86_64VaesTo
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZ
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZDec
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

/-!
# XTS-AES on x86-64 with AVX-512 VAES, sixteen blocks at a time

`vg_aes_xts_encrypt_vaes_vpclmul_avx512` and
`vg_aes_xts_decrypt_vaes_vpclmul_avx512`, in place (the arguments of
`X86_64Vaes.lean`), and their out-of-place counterparts
`vg_aes_xts_encrypt_to_vaes_vpclmul_avx512` and
`vg_aes_xts_decrypt_to_vaes_vpclmul_avx512` (those of `X86_64VaesTo.lean`):
the one-pass functions of `X86_64Vaes.lean` and `X86_64VaesTo.lean`, with
a loop over sixteen blocks before their eight-block loop (`loop16`).

The sixteen-block loop holds the blocks four to a 512-bit register,
`zmm0`–`zmm3`, and their tweaks in `zmm4`–`zmm7`: lane `l` of `zmm4 + k`
holds the tweak of block `4 k + l` of the group. Each block is loaded once,
has its tweak XORed in, is enciphered (or deciphered) with each round key
broadcast into the four lanes of `zmm8` (`VaesZ.aesZ`, `VaesZDec.aesDecZ`),
has its tweak XORed in again and is stored. The next group's tweaks are
the last eight's times `α⁸` (`stepZ`: a byte shift of each lane, and the
byte shifted out times `0x87`, carry-less, from `zmm11`), then those times
`α⁸`, as OpenSSL's AVX-512 XTS (from Intel's ISA-L) computes them. The loop
starts from the tweaks of the first eight blocks in the scratch buffer,
where the eight-block loop keeps them, and leaves those of the eight blocks
after it there, so the eight-block loop and the blocks left go on from
there unchanged.

Every branch and every address depends only on the pointers, `rounds` and
`n`. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64VaesZ

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.AesXts.X86_64Vaes (bufOff)

/-- The block registers, four blocks each. -/
def regsZ : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]

/-- The tweak registers: lane `l` of `twsZ[k]` holds the tweak of block
`4 k + l` of the group. -/
def twsZ : List XReg := [.xmm4, .xmm5, .xmm6, .xmm7]

/-- `0x87` into the low quadword of the four lanes of `zmm11`. -/
def constKZ : List Instr := [.movImm64 .rax 0x87, .vop (.vmovq .xmm11 .rax), .zop (.vpbroadcastq .xmm11 .xmm11)]

/-- `d := t · α⁸` in each lane: the lane shifted left a byte, and the byte
shifted out times `0x87`, carry-less, XORed in. -/
def stepZ (d t : XReg) : List Instr :=
  [.zop (.vpsrldq .xmm10 t 15), .zop (.vpclmulqdq .xmm10 .xmm10 .xmm11 0), .zop (.vpslldq .xmm9 t 1),
   .zop (.zbin .vpxord d .xmm9 .xmm10)]

/-- The next group's tweaks: blocks `16 … 23` from blocks `8 … 15`, then
blocks `24 … 31` from those. -/
def stepsZ : List Instr := stepZ .xmm4 .xmm6 ++ stepZ .xmm5 .xmm7 ++ stepZ .xmm6 .xmm4 ++ stepZ .xmm7 .xmm5

/-- The tweaks of the first eight blocks from the scratch buffer, and those
of the next eight from them. -/
def ldTZ : List Instr :=
  [.vmovdqu32Load .xmm4 (at_ .r8 bufOff), .vmovdqu32Load .xmm5 (at_ .r8 (bufOff + 64))] ++
    stepZ .xmm6 .xmm4 ++ stepZ .xmm7 .xmm5

/-- The tweaks of the first eight blocks left back to the scratch buffer. -/
def stTZ : List Instr := [.vmovdqu32Store (at_ .r8 bufOff) .xmm4, .vmovdqu32Store (at_ .r8 (bufOff + 64)) .xmm5]

/-- Load block register `bs[i]` from the blocks at `ld (64 (k + i))` and XOR
in their tweaks, `ts[i]`. -/
def preZ (ld : Nat → MemOp) : List XReg → List XReg → Nat → List Instr
  | b :: bs, t :: ts, k => ([.vmovdqu32Load b (ld (64 * k)), .zop (.zbin .vpxord b b t)] : List Instr) ++
      preZ ld bs ts (k + 1)
  | _, _, _ => []

/-- XOR the tweaks `ts[i]` into block register `bs[i]` again and store it
to the blocks at `r11 + 64 (k + i)`. -/
def postZ : List XReg → List XReg → Nat → List Instr
  | b :: bs, t :: ts, k => ([.zop (.zbin .vpxord b b t), .vmovdqu32Store (at_ .r11 (64 * k)) b] : List Instr) ++
      postZ bs ts (k + 1)
  | _, _, _ => []

/-- One group of sixteen blocks, loaded from `ld`, through the rounds `f`. -/
def group16 (ld : Nat → MemOp) (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (preZ ld regsZ twsZ 0))
    (.seq (f regsZ)
      (.block (postZ regsZ twsZ 0 ++ stepsZ ++ ([.alu .add .r11 (.imm 256), .alu .sub .r9 (.imm 16),
        .alu .cmp .r9 (.imm 16)] : List Instr))))

/-- The sixteen-block loop, while sixteen blocks are left (`cmp r9, 16`
done). -/
def loop16 (ld : Nat → MemOp) (f : List XReg → Prog isa) : Prog isa :=
  .ite .b (.block [])
    (.seq (.block (constKZ ++ ldTZ)) (.seq (.loop (group16 ld f) .ae) (.block stTZ)))

/-- The blocks while eight are left: sixteen at a time through `f16`, then
eight through `L8` (which starts with `cmp r9, 8` done). -/
def loops (ld : Nat → MemOp) (f16 : List XReg → Prog isa) (L8 : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 16)])
    (.seq (loop16 ld f16) (.seq (.block [.vop .vzeroupper, .alu .cmp .r9 (.imm 8)]) L8))

/-- The blocks of the in-place functions, at `r11`. -/
def ldIn (d : Nat) : MemOp := at_ .r11 d

def encrypt : Prog isa :=
  X86_64Vaes.crypt (.block [])
    (loops ldIn (Aes.X86_64.VaesZ.aesZ .xmm8) (X86_64Vaes.loop8 Aes.X86_64.Vaes.aes)) Aes.X86_64.AesNi.aes

def decrypt : Prog isa :=
  X86_64Vaes.crypt Aes.X86_64.AesNi.imcKeys
    (loops ldIn (Aes.X86_64.VaesZDec.aesDecZ .xmm8) (X86_64Vaes.loop8 Aes.X86_64.VaesBlocks.aesDec))
    Aes.X86_64.AesNi.aesDec

def encryptTo : Prog isa :=
  X86_64VaesTo.crypt (.block [])
    (loops X86_64VaesTo.ix (Aes.X86_64.VaesZ.aesZ .xmm8) (X86_64VaesTo.loop8 Aes.X86_64.Vaes.aes))
    Aes.X86_64.AesNi.aes

def decryptTo : Prog isa :=
  X86_64VaesTo.crypt Aes.X86_64.AesNi.imcKeys
    (loops X86_64VaesTo.ix (Aes.X86_64.VaesZDec.aesDecZ .xmm8) (X86_64VaesTo.loop8 Aes.X86_64.VaesBlocks.aesDec))
    Aes.X86_64.AesNi.aesDec

end VG.Impl.AesXts.X86_64VaesZ
