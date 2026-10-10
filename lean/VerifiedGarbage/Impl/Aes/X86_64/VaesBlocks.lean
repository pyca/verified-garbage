import VerifiedGarbage.Impl.Aes.X86_64.Vaes
import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks

/-!
# AES with VAES on x86-64: encryption and decryption of whole blocks

`vg_aes_encrypt_blocks_vaes(schedule = rdi, rounds = rsi, data = rdx, n = rcx, scratch = r8)`
and `vg_aes_decrypt_blocks_vaes`, with the contracts of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`),
for CPUs with VAES and AVX2 (and AES-NI, for the blocks left).

As `vg_aes_ctr32_vaes` (`Vaes.lean`) does: sixteen blocks at a time, two in
each of `ymm0`–`ymm7`, loaded from the data and stored back in place, each
round key broadcast once into both lanes of `ymm8` and applied to all eight
registers by the VEX.256 `vaesenc` (or `vaesdec`), with a branch on the
public `rounds` around rounds 10–13. Then `vzeroupper` clears the upper
lanes, and the blocks left (fewer than sixteen) go through
`vg_aes_encrypt_blocks_aesni`'s (or `vg_aes_decrypt_blocks_aesni`'s) loops,
eight and then one at a time (`AesNi.blocksTail`).

Decryption runs FIPS 197's equivalent inverse cipher (§5.3.5), as
`vg_aes_decrypt_blocks_aesni` does: the middle round keys through `aesimc`
are computed once, into `scratch + 16 j` for round key `j` (`1 ≤ j < Nr`),
before the blocks (`AesNi.imcKeys`), and both loops read them from there.

No callee-saved register is written. Every branch and every address
depends only on the pointers, `rounds` and `n`.
-/

namespace VG.Impl.Aes.X86_64.VaesBlocks

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ blocksTail imcKeys)
open VG.Impl.Aes.X86_64.Vaes (keyOpK regs8)

/-- Load the data blocks `rdx + 32 (j + i)` and the next into the block
registers, two in each. -/
def loadData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .vmovdquLoad .l256 b (at_ .rdx (32 * j)) :: loadData bs (j + 1)

/-- Store the block registers to the data blocks `rdx + 32 (j + i)` and the
next. -/
def storeData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .vmovdquStore .l256 (at_ .rdx (32 * j)) b :: storeData bs (j + 1)

/-- `r10 := rdi + 16 rsi`, the last round key; then `cmp rcx, 16`. -/
def blocksLoad : List Instr :=
  [.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .alu .cmp .rcx (.imm 16)]

/-- Sixteen blocks through `f`. -/
def blocks16 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (loadData regs8 0))
    (.seq (f regs8)
      (.block (storeData regs8 0 ++ ([.alu .add .rdx (.imm 256), .alu .sub .rcx (.imm 16),
        .alu .cmp .rcx (.imm 16)] : List Instr))))

/-- The blocks: sixteen at a time through `f16`, then the AES-NI loops
through `f`. -/
def blocks (f16 f : List XReg → Prog isa) : Prog isa :=
  .seq (.block blocksLoad)
    (.seq (.ite .b (.block []) (.loop (blocks16 f16) .ae))
      (.seq (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 8)]) (blocksTail f)))

def encryptBlocks : Prog isa := blocks Vaes.aes AesNi.aes

/-- The middle round with round key `j` (`1 ≤ j < Nr`) of both lanes of each
block register, from `scratch + 16 j`. -/
def dround (regs : List XReg) (j : Nat) : List Instr := keyOpK .xmm8 regs .vaesdec (at_ .r8 (16 * j))

/-- The inverse cipher on both lanes of each block register, with `rounds`
in `rsi`, the key schedule at `rdi`, its last round key at `r10`, and round
keys 1 … `Nr − 1` through `aesimc` in the scratch buffer at `r8`. -/
def aesDec (regs : List XReg) : Prog isa :=
  .seq (.block (keyOpK .xmm8 regs .vpxor (at_ .r10 0) ++ ([.alu .cmp .rsi (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10)))))
      (.block ((List.range 9).flatMap (fun j => dround regs (9 - j)) ++
        keyOpK .xmm8 regs .vaesdeclast (at_ .rdi 0))))

def decryptBlocks : Prog isa := .seq imcKeys (blocks aesDec AesNi.aesDec)

end VG.Impl.Aes.X86_64.VaesBlocks
