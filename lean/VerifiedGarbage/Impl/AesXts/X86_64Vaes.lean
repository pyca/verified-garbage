module

public import VerifiedGarbage.Impl.AesXts.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

/-!
# XTS-AES on x86-64 in one pass, with VAES and VPCLMULQDQ

`vg_aes_xts_encrypt_vaes_vpclmul(schedule = rdi, rounds = rsi, tweak = rdx, data = rcx, n = r8,
scratch = r9)` and `vg_aes_xts_decrypt_vaes_vpclmul`, with the contracts of
`vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` (`Spec/Xts/Contract.lean`), for
CPUs with VAES, VPCLMULQDQ and AVX2 (and AES-NI). Unlike `vg_aes_xts_encrypt`
(`X86_64.lean`), they call no block function: each block is read once, has
its tweak XORed in, is enciphered (or deciphered) and has its tweak XORed in
again before it is stored.

The arguments are moved so that the round code of `vg_aes_encrypt_blocks_vaes`
and `vg_aes_encrypt_blocks_aesni` (`Impl/Aes/X86_64/`) finds them where it
expects them: the schedule in `rdi`, `rounds` in `rsi`, the last round key at
`r10`, and the scratch buffer (where decryption keeps the round keys through
`aesimc`, `AesNi.imcKeys`) in `r8`; the data pointer goes to `r11` and the
number of blocks left to `r9`, and the tweak pointer stays in `rdx`.

The tweaks of the next sixteen blocks are kept at `scratch + 256`, the tweak
of block `j` at `scratch + 256 + 16 j`. The first sixteen are computed one
after the other in `rax` and `rcx` (`gen`), as `vg_aes_xts_encrypt` computes
them (`AesXts.X86_64.mulA`, with `r10` for the mask, `mulAr`). Then, sixteen blocks at a time, two in each of
`ymm0`–`ymm7`: each block register is loaded from the data and XORed with its
two tweaks (`preXor`), AES runs on all eight (`Vaes.aes`, or
`VaesBlocks.aesDec`), each is XORed with its tweaks again and stored
(`postXor`), and each pair of tweaks is multiplied by `α¹⁶` in place
(`stepT`): `T ⊗ α¹⁶` is `T` shifted left by sixteen bits (`vpslldq` by two
bytes) XORed with the carry-less product of its top sixteen bits
(`vpsrldq` by fourteen bytes) and `0x87` (`vpclmulqdq` with `0x87` in each
lane of `ymm11`). After the last such group, `vzeroupper`, and the blocks
left (fewer than sixteen) go through the AES-NI round code, eight and then
one at a time (`tail`), with their tweaks from the same buffer, read through
`rax`. The tweak after the last block, at `rax` then, is copied to the
tweak pointer.

Every branch and every address depends only on the pointers, `rounds` and
`n`. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64Vaes

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Aes.X86_64.Vaes (regs8)

/-- Where the tweaks are kept, in the scratch buffer. -/
def bufOff : Nat := 256

/-- The arguments moved, and the tweak loaded into `rax` and `rcx`. -/
def enter : List Instr :=
  [.mov .r11 (.reg .rcx), .mov .rax (.reg .r8), .mov .r8 (.reg .r9), .mov .r9 (.reg .rax),
   .mov .rax (.mem (at_ .rdx 0)), .mov .rcx (.mem (at_ .rdx 8))]

/-- The tweak in `rax` and `rcx` times `α`, as `AesXts.X86_64.mulA` computes
it, with the mask in `r10`. -/
def mulAr : List Instr :=
  [.mov .r10 (.reg .rcx), .alu .add .r10 (.reg .r10), .alu .sbb .r10 (.reg .r10), .alu .and .r10 (.imm 0x87),
   .alu .add .rax (.reg .rax), .alu .adc .rcx (.reg .rcx), .alu .xor .rax (.reg .r10)]

/-- The tweak in `rax` and `rcx` stored as that of block `j`, and multiplied
by `α`. -/
def genStep (j : Nat) : List Instr :=
  ([.store (at_ .r8 (bufOff + 16 * j)) .rax, .store (at_ .r8 (bufOff + 16 * j + 8)) .rcx] : List Instr) ++ mulAr

/-- The tweaks of blocks 0 … 15, then the last round key's address into
`r10`. -/
def gen : List Instr :=
  (List.range 16).flatMap genStep ++
  ([.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] : List Instr)

/-- `0x87` into the low quadword of both lanes of `ymm11`. -/
def constK : List Instr :=
  [.movImm64 .rax 0x87, .vop (.vmovq .xmm11 .rax), .vop (.vinserti128 .xmm11 .xmm11 .xmm11 1)]

/-- Load block register `i` from the data blocks `r11 + 32 (k + i)` and the
next, and XOR in their tweaks. -/
def preXor : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => ([.vmovdquLoad .l256 b (at_ .r11 (32 * k)),
      .vbinLoad .vpxor .l256 b b (at_ .r8 (bufOff + 32 * k))] : List Instr) ++ preXor bs (k + 1)

/-- XOR the tweaks into block register `i` again, and store it to the data
blocks `r11 + 32 (k + i)` and the next. -/
def postXor : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => ([.vbinLoad .vpxor .l256 b b (at_ .r8 (bufOff + 32 * k)),
      .vmovdquStore .l256 (at_ .r11 (32 * k)) b] : List Instr) ++ postXor bs (k + 1)

/-- The tweaks of blocks `2 k` and `2 k + 1` times `α¹⁶`. -/
def stepT (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm9 (at_ .r8 (bufOff + 32 * k)), .vop (.vshift .psrldq .l256 .xmm10 .xmm9 14),
   .vop (.vpclmulqdq .l256 .xmm10 .xmm10 .xmm11 0), .vop (.vshift .pslldq .l256 .xmm9 .xmm9 2),
   .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm10), .vmovdquStore .l256 (at_ .r8 (bufOff + 32 * k)) .xmm9]

/-- All sixteen tweaks times `α¹⁶`. -/
def steps : List Instr := (List.range 8).flatMap stepT

/-- Sixteen blocks through `f`. -/
def group (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (preXor regs8 0))
    (.seq (f regs8)
      (.block (postXor regs8 0 ++ steps ++ ([.alu .add .r11 (.imm 256), .alu .sub .r9 (.imm 16),
        .alu .cmp .r9 (.imm 16)] : List Instr))))

/-- Load block register `i` from the data block `r11 + 16 (k + i)`, and XOR
in its tweak from `rax + 16 (k + i)`. -/
def tPre : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => ([.movdquLoad b (at_ .r11 (16 * k)), .vbinLoad .vpxor .l128 b b (at_ .rax (16 * k))] : List Instr) ++
      tPre bs (k + 1)

/-- XOR the tweak into block register `i` again, and store it to the data
block `r11 + 16 (k + i)`. -/
def tPost : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => ([.vbinLoad .vpxor .l128 b b (at_ .rax (16 * k)), .movdquStore (at_ .r11 (16 * k)) b] : List Instr) ++
      tPost bs (k + 1)

/-- Eight blocks through `f`. -/
def tail8 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (tPre regs8 0))
    (.seq (f regs8)
      (.block (tPost regs8 0 ++ ([.alu .add .r11 (.imm 128), .alu .add .rax (.imm 128),
        .alu .sub .r9 (.imm 8)] : List Instr))))

/-- One block through `f`. -/
def tail1 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (tPre [.xmm0] 0))
    (.seq (f [.xmm0])
      (.block (tPost [.xmm0] 0 ++ ([.alu .add .r11 (.imm 16), .alu .add .rax (.imm 16),
        .alu .sub .r9 (.imm 1)] : List Instr))))

/-- The blocks left (fewer than sixteen), eight and then one at a time, their
tweaks from `scratch + 256` on. -/
def tail (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.reg .r8), .alu .add .rax (.imm 256), .alu .cmp .r9 (.imm 8)])
    (.seq (.ite .b (.block []) (tail8 f))
      (.seq (.block [.alu .test .r9 (.reg .r9)]) (.ite .e (.block []) (.loop (tail1 f) .ne))))

/-- The tweak after the last block, at `rax`, copied to the tweak pointer. -/
def finish : List Instr :=
  [.mov .rcx (.mem (at_ .rax 0)), .store (at_ .rdx 0) .rcx, .mov .rcx (.mem (at_ .rax 8)), .store (at_ .rdx 8) .rcx]

/-- All the blocks (at least one), the rounds of sixteen through `f16` and
those of the rest through `f`, after `pre` (with the tweaks computed). -/
def crypt (pre : Prog isa) (f16 f : List XReg → Prog isa) : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)])
    (.ite .e (.block [])
      (.seq (.block (enter ++ gen))
        (.seq pre
          (.seq (.block [.alu .cmp .r9 (.imm 16)])
            (.seq (.ite .b (.block []) (.seq (.block constK) (.seq (.loop (group f16) .ae) (.block [.vop .vzeroupper]))))
              (.seq (tail f) (.block finish)))))))

def encrypt : Prog isa := crypt (.block []) Aes.X86_64.Vaes.aes Aes.X86_64.AesNi.aes

def decrypt : Prog isa := crypt Aes.X86_64.AesNi.imcKeys Aes.X86_64.VaesBlocks.aesDec Aes.X86_64.AesNi.aesDec

end VG.Impl.AesXts.X86_64Vaes
