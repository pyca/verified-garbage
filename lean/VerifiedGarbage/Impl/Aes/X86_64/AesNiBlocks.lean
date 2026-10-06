import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES with AES-NI on x86-64: encryption and decryption of whole blocks

`vg_aes_encrypt_blocks_aesni(schedule = rdi, rounds = rsi, data = rdx, n = rcx, scratch = r8)`
and `vg_aes_decrypt_blocks_aesni`, with the contracts of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`),
for CPUs with AES-NI.

As `vg_aes_ctr32_aesni` (`AesNi.lean`) does: eight blocks at a time
(`xmm0`–`xmm7`), each round key loaded once into `xmm8` and applied to all
eight, then the remaining blocks one at a time, with a branch on the public
`rounds` around rounds 10–13; here each group of blocks is loaded from the
data and stored back in place.

Decryption runs FIPS 197's equivalent inverse cipher (§5.3.5), which is
what `aesdec` computes: the middle rounds take `InvMixColumns` of the round
keys (`aesimc`), which are computed once, into `scratch + 16 j` for round
key `j` (`1 ≤ j < Nr`), before the blocks.

No callee-saved register is written. Every branch and every address
depends only on the pointers, `rounds` and `n`.
-/

namespace VG.Impl.Aes.X86_64.AesNi

open VG.X86_64

/-- Load the data blocks `rdx + 16 (j + i)` into the block registers. -/
def loadData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .movdquLoad b (at_ .rdx (16 * j)) :: loadData bs (j + 1)

/-- Store the block registers to the data blocks `rdx + 16 (j + i)`. -/
def storeData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .movdquStore (at_ .rdx (16 * j)) b :: storeData bs (j + 1)

/-- `r10 := rdi + 16 rsi`, the last round key; then `cmp rcx, 8`. -/
def blocksLoad : List Instr :=
  [.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .alu .cmp .rcx (.imm 8)]

/-- Eight blocks through `f`. -/
def blocks8 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (loadData regs8 0))
    (.seq (f regs8)
      (.block (storeData regs8 0 ++ [.alu .add .rdx (.imm 128), .alu .sub .rcx (.imm 8),
        .alu .cmp .rcx (.imm 8)])))

/-- One block through `f`. -/
def blocks1 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (loadData [.xmm0] 0))
    (.seq (f [.xmm0])
      (.block (storeData [.xmm0] 0 ++ [.alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)])))

/-- The blocks, eight and then one at a time, after `cmp rcx, 8`. -/
def blocksTail (f : List XReg → Prog isa) : Prog isa :=
  .seq (.ite .b (.block []) (.loop (blocks8 f) .ae))
    (.seq (.block [.alu .test .rcx (.reg .rcx)]) (.ite .e (.block []) (.loop (blocks1 f) .ne)))

def encryptBlocks : Prog isa := .seq (.block blocksLoad) (blocksTail aes)

/-- `InvMixColumns` of round key `j` into `scratch + 16 j`. -/
def imcKey (j : Nat) : List Instr :=
  [.movdquLoad .xmm8 (at_ .rdi (16 * j)), .xop (.bin .aesimc .xmm8 .xmm8),
   .movdquStore (at_ .r8 (16 * j)) .xmm8]

/-- Round keys 1 … `Nr − 1` through `aesimc`, for `rounds` (10, 12 or 14) in `rsi`. -/
def imcKeys : Prog isa :=
  .seq (.block ((List.range 9).flatMap (fun j => imcKey (j + 1)) ++ [.alu .cmp .rsi (.imm 10)]))
    (.ite .e (.block [])
      (.seq (.block (imcKey 10 ++ imcKey 11 ++ [.alu .cmp .rsi (.imm 12)]))
        (.ite .e (.block []) (.block (imcKey 12 ++ imcKey 13)))))

/-- The middle round with round key `j` (`1 ≤ j < Nr`) of each block, from
`scratch + 16 j`. -/
def dround (regs : List XReg) (j : Nat) : List Instr := keyOp regs .aesdec (at_ .r8 (16 * j))

/-- The inverse cipher on each block register, with `rounds` in `rsi`, the
key schedule at `rdi`, its last round key at `r10`, and round keys
1 … `Nr − 1` through `aesimc` in the scratch buffer at `r8`. -/
def aesDec (regs : List XReg) : Prog isa :=
  .seq (.block (keyOp regs .pxor (at_ .r10 0) ++ [.alu .cmp .rsi (.imm 10)]))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10)))))
      (.block ((List.range 9).flatMap (fun j => dround regs (9 - j)) ++
        keyOp regs .aesdeclast (at_ .rdi 0))))

def decryptBlocks : Prog isa := .seq imcKeys (.seq (.block blocksLoad) (blocksTail aesDec))

end VG.Impl.Aes.X86_64.AesNi
