module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# AES-GCM-SIV: x86-64 implementation

`vg_aes_gcm_siv_seal(schedule = rdi, rounds = rsi, nonce = rdx, aad = rcx, aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16], work = [rsp + 24])`
and `vg_aes_gcm_siv_open` with the same arguments (`Spec/GcmSiv/Contract.lean`),
with the working space `work` as a last argument, which a frame on the stack
allocates (`Impl.StackScratch.X86_64.withStackArgScratch`), composed of calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key`,
`vg_ghash` and `vg_aes_encrypt_blocks`, and generic over their
implementations as AES-GCM is (`Impl.AesGcm.X86_64.Callees`: only `ctr`,
`key` and `gh` are called), with the implementation of
`vg_aes_encrypt_blocks` that goes with `ctr` (`e`).

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), all by one
  call of `vg_aes_encrypt_blocks` on those blocks at `W + 488`, of which the
  first 8 bytes are kept, one after the other from `W + 16` (`derive`): the
  authentication key at `W + 16`, the encryption key at `W + 32`; the
  encryption key is expanded by `vg_aes_expand_key`, for the same number of
  rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: each block is
  copied to `W + 488` with its bytes reversed before `vg_ghash` absorbs it
  (`absorb`), up to 64 at a time; the lengths block is written in GHASH's
  order (`lens`), and the result is read back reversed (`tagIn`).
* The tag is `vg_aes_ctr32` of the tag input on a zero block (`tag`).
* Counter mode (§4) increments the first 4 bytes of the counter block, as a
  little-endian number, which `vg_aes_ctr32` (which increments the last 4,
  big-endian) does not: up to 64 whole blocks at a time, their counter
  blocks are written to `W + 488` from an SSE register whose first 32-bit
  lane `paddd` increments (`ctrGen`), encrypted in place by one call of
  `vg_aes_encrypt_blocks` and XORed into the data 16 bytes at a time
  (`ksXor`); the last bytes are XORed with a keystream block from
  `vg_aes_ctr32` (`crypt`).
* With `wide` (the instances whose callees need AVX2), the copies are
  reversed and the keystream XORed four blocks at a time, two in each of two
  256-bit loads (`revLoopY`, `ksLoop`, `quadsThenOnes`) when a chunk has
  eight or more, and the blocks left one at a time as without it.
* `seal` copies the tag from `W` to `tag` at the end (`tagOut`); `open`
  copies the received tag from `tag` to `W` first (`recv`), computes the tag of the plaintext at `W + 128` and compares the two
  without a branch (`cmp`), then masks the data with `0 − ok`, 16 bytes at
  a time and then its last `len mod 16` bytes (`mask`).

## The working space `W` (3816 bytes)

* `[0, 16)`: the tag (the one `seal` computes, or the received one);
  `[16, 32)`: the authentication key; `[32, 64)`: the encryption key;
  `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator; `[96, 112)`: the
  counter block (or the tag input); `[112, 128)`: a copy of it for a call;
  `[128, 144)`: a block (and the tag `open` computes); `[144, 192)`: our
  caller's `rbx, rbp, r12–r15`; `[192, 200)`: `ok`; `[200, 248)`: the public
  arguments;
* `[248, 488)`: the encryption key's schedule; `[488, 1512)`: the reversed
  blocks (or the counter blocks); `[1512, 1768)`: `vg_ghash`'s working
  space; `[1768, 3816)`: `vg_aes_ctr32`'s and `vg_aes_encrypt_blocks`'s, and
  `vg_aes_expand_key`'s at its start.

`tag`'s address stays on the stack, at `[rsp + 16]`.

`r15` holds `W` and `r13` the key schedule throughout; the functions called
preserve them, and `rbx`, `rbp`, `r12` and `r14`, which hold lengths,
pointers and counts across calls. Only the pointers, the lengths and
`rounds` (and for `open`, whether the tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop xorLoop Callees Fn maskTail)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cmO : Nat := 96
def ccO : Nat := 112
def bO : Nat := 128
def okO : Nat := 192
def roundsO : Nat := 200
def nonceO : Nat := 208
def aadO : Nat := 216
def alenO : Nat := 224
def dataO : Nat := 232
def lenO : Nat := 240
def skO : Nat := 248
def revO : Nat := 488
def ghO : Nat := 1512
def scrO : Nat := 1768

/-- Where our caller's callee-saved registers are kept. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 144), (.rbp, 152), (.r12, 160), (.r13, 168), (.r14, 176), (.r15, 184)]

def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr :=
  [.mov32 .rax (imm 0), .store (at_ .r15 d) .rax, .store (at_ .r15 (d + 8)) .rax]

/-- The 16 bytes at `W + s` copied to `W + d`. -/
def copy16 (s d : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r15 s)), .store (at_ .r15 d) .rax, .mov .rax (.mem (at_ .r15 (s + 8))),
    .store (at_ .r15 (d + 8)) .rax]

variable (c : Callees)

def callCtr : Prog isa := .call c.ctr.name c.ctr.code
def callKey : Prog isa := .call c.key.name c.key.code
def callGh : Prog isa := .call c.gh.name c.gh.code

variable (e : Fn)

/-- The call of `vg_aes_encrypt_blocks`. -/
def callEcb : Prog isa := .call e.name e.code

/-- `vg_aes_ctr32`'s arguments but the key schedule: one block at `rcx`, the
counter block at `W + ccO` and the working space. -/
def ctrArgs : List Instr :=
  ([.mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 ccO ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO

/-! ## The keys -/

/-- `little_endian_uint32(rbx) ‖ nonce` at `rdi`. -/
def deriveBlock : List Instr :=
  [.mov .rax (.mem (at_ .r15 nonceO)), .mov32 .rcx (.mem (at_ .rax 0)), .mov32 .rdx (.mem (at_ .rax 4)),
    .mov32 .r8 (.mem (at_ .rax 8)), .store32 (at_ .rdi 0) .rbx, .store32 (at_ .rdi 4) .rcx,
    .store32 (at_ .rdi 8) .rdx, .store32 (at_ .rdi 12) .r8]

/-- The `rbp` blocks `little_endian_uint32(i) ‖ nonce` from `W + revO`, for
`i` from 0. -/
def deriveBlocks : Prog isa :=
  .seq (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .rdi .r15 revO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr)))
    (.loop (.block (deriveBlock ++ ([.alu .add .rdi (imm 16), .alu .add .rbx (imm 1), .alu .cmp .rbx (.reg .rbp)] :
      List Instr))) .ne)

/-- `vg_aes_encrypt_blocks`'s arguments for the message keys: the
key-generating key's schedule, the `rbp` blocks at `W + revO` and the working
space. -/
def deriveArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 revO ++
    ([.mov .rcx (.reg .rbp)] : List Instr) ++ ptr .r8 .r15 scrO

/-- The first 8 bytes of each of the `rbp` encrypted blocks at `W + revO`,
one after the other from `W + akO`. -/
def deriveKeep : Prog isa :=
  .seq (.block (ptr .rsi .r15 revO ++ ptr .rdi .r15 akO ++ ([.mov .rcx (.reg .rbp)] : List Instr)))
    (.loop (.block [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rsi (imm 16),
      .alu .add .rdi (imm 8), .alu .sub .rcx (imm 1)]) .ne)

/-- The message keys (all their blocks encrypted by one call of
`vg_aes_encrypt_blocks`), 8 bytes per block, from `W + akO`. -/
def derive : Prog isa :=
  .seq deriveBlocks (.seq (.block deriveArgs) (.seq (callEcb e) deriveKeep))

/-- The encryption key's schedule at `W + skO`: its length is
`4 (rounds − 6)`. -/
def expand : Prog isa :=
  .seq (.block (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO))
    (callKey c)

/-- GHASH's key, `H · x` for the authentication key `H` (as a
little-endian number), in GHASH's order at `W + hO`, and its accumulator
zeroed. -/
def hkey : List Instr :=
  ([.mov .rax (.mem (at_ .r15 akO)), .mov .rdx (.mem (at_ .r15 (akO + 8))), .mov .rcx (.reg .rax),
    .alu .and .rcx (imm 1), .mov32 .r8 (imm 0), .alu .sub .r8 (.reg .rcx), .shift .shr .rax 1,
    .mov .rcx (.reg .rdx), .alu .and .rcx (imm 1), .shift .ror .rcx 1, .alu .or .rax (.reg .rcx), .shift .shr .rdx 1,
    .movImm64 .rcx 0xE100000000000000, .alu .and .rcx (.reg .r8), .alu .xor .rdx (.reg .rcx), .bswap .rdx,
    .bswap .rax, .store (at_ .r15 hO) .rdx, .store (at_ .r15 (hO + 8)) .rax] : List Instr) ++ zero16 yO

/-! ## POLYVAL -/

/-- `vg_ghash`'s arguments but the blocks and their number. -/
def ghArgs : List Instr := ptr .rdi .r15 hO ++ ptr .rsi .r15 yO ++ ptr .r8 .r15 ghO

/-- The `r14` (at least 1) blocks at `rsi` copied to `rdi`, the bytes of
each reversed. -/
def revLoop : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r14)])
    (.loop (.block [.mov .rax (.mem (at_ .rsi 0)), .mov .rdx (.mem (at_ .rsi 8)), .bswap .rax, .bswap .rdx,
      .store (at_ .rdi 0) .rdx, .store (at_ .rdi 8) .rax, .alu .add .rsi (imm 16), .alu .add .rdi (imm 16),
      .alu .sub .rcx (imm 1)]) .ne)

/-- The mask with which `vpshufb` reverses the bytes of each 128-bit lane, in
both lanes of `ymm1` (through `rax` and `xmm12`). -/
def revMaskY : List Instr :=
  Impl.Gcm.X86_64.Pclmul.const .xmm1 Impl.Gcm.X86_64.Pclmul.revMask ++
    ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr)

/-- Two blocks at `rsi + d` copied to `rdi + d`, the bytes of each reversed. -/
def rev2 (d : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rsi d), .vop (.vbin .vpshufb .l256 .xmm0 .xmm0 .xmm1),
    .vmovdquStore .l256 (at_ .rdi d) .xmm0]

/-- Four blocks at `rsi` copied to `rdi`, the bytes of each reversed; `rcx`
four fewer, compared with 4. -/
def revQuad : List Instr :=
  rev2 0 ++ rev2 32 ++
    ([.alu .add .rsi (imm 64), .alu .add .rdi (imm 64), .alu .sub .rcx (imm 4), .alu .cmp .rcx (imm 4)] : List Instr)

/-- The body of `revLoop`: one block at `rsi` copied to `rdi`, its bytes
reversed; `rcx` one fewer. -/
def revOne : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .rdx (.mem (at_ .rsi 8)), .bswap .rax, .bswap .rdx,
    .store (at_ .rdi 0) .rdx, .store (at_ .rdi 8) .rax, .alu .add .rsi (imm 16), .alu .add .rdi (imm 16),
    .alu .sub .rcx (imm 1)]

/-- The `rcx` (at least 1) blocks: if there are eight or more, four at a time
with `quad` while there are four (after `pre`); then one at a time with
`one`. Below eight, the setup and `vzeroupper` cost more than the quads save,
and no 256-bit register gets used; `vzeroupper` after the quads keeps the
SSE instructions after them (and in the functions called later) from paying
for their dirty upper halves. -/
def quadsThenOnes (pre quad one : List Instr) : Prog isa :=
  .seq (.block [.alu .cmp .rcx (imm 8)])
  (.ite .b (.loop (.block one) .ne)
    (.seq (.block pre) (.seq (.loop (.block quad) .ae) (.seq (.block [.vop .vzeroupper])
      (.seq (.block [.alu .test .rcx (.reg .rcx)]) (.ite .e (.block []) (.loop (.block one) .ne)))))))

/-- `revLoop` four blocks at a time on 256-bit registers, then one at a
time. -/
def revLoopY : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r14)]) (quadsThenOnes revMaskY revQuad revOne)

/-- `revLoop`, or `revLoopY` if `wide`. -/
def revSel (wide : Bool) : Prog isa := if wide then revLoopY else revLoop

/-- Up to 64 of the `rbx` whole blocks at `r12` (`r14` of them), reversed and
absorbed; `r12` and `rbx` past them. -/
def absorbChunk (wide : Bool) : Prog isa :=
  .seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
  (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
  (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
  (.seq (revSel wide)
  (.seq (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr)))
  (.seq (callGh c)
    (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)]))))))

/-- The last `rbp` (1 to 15) bytes at `r12`, padded with zeros, reversed and
absorbed. -/
def absorbTail : Prog isa :=
  .seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)] : List Instr)))
  (.seq copyLoop
  (.seq (.block (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx,
      .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] : List Instr) ++ ghArgs ++ ptr .rdx .r15 revO ++
      ([.mov32 .rcx (imm 1)] : List Instr)))
    (callGh c)))

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, absorbed. -/
def absorb (wide : Bool) : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (absorbChunk c wide) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (absorbTail c))))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, in GHASH's order
at `W + bO`, absorbed. -/
def lens : Prog isa :=
  .seq (.block (([.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 bO) .rax,
      .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] : List Instr) ++
      ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr)))
    (callGh c)

/-- The tag input at `W + cmO`: POLYVAL's result in its own order, its first
12 bytes XORed with the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.mov .rax (.mem (at_ .r15 (yO + 8))), .bswap .rax, .mov .rdx (.mem (at_ .r15 yO)), .bswap .rdx,
    .mov .rcx (.mem (at_ .r15 nonceO)), .alu .xor .rax (.mem (at_ .rcx 0)), .mov32 .r8 (.mem (at_ .rcx 8)),
    .alu .xor .rdx (.reg .r8), .movImm64 .r8 0x7FFFFFFFFFFFFFFF, .alu .and .rdx (.reg .r8),
    .store (at_ .r15 cmO) .rax, .store (at_ .r15 (cmO + 8)) .rdx]

/-- The tag, the encryption of the tag input, at `W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o))
    (callCtr c)

/-! ## Counter mode -/

/-- The counter blocks `CB_j, …, CB_{j + r14 − 1}` written from `W + revO`:
the counter block in `xmm0`, stored and its first 32-bit word incremented
(`paddd` of `xmm1`, which holds 1 in its first word and 0 in the others)
`r14` times (`rcx` counting down); then the block back at `W + cmO`. -/
def ctrGen : Prog isa :=
  .seq (.block (([.movdquLoad .xmm0 (at_ .r15 cmO), .mov32 .r8 (imm 1), .xop (.movq .xmm1 .r8),
      .mov .rcx (.reg .r14)] : List Instr) ++ ptr .rdi .r15 revO))
    (.seq (.loop (.block [.movdquStore (at_ .rdi 0) .xmm0, .xop (.bin .paddd .xmm0 .xmm1), .alu .add .rdi (imm 16),
        .alu .sub .rcx (imm 1)]) .ne)
      (.block [.movdquStore (at_ .r15 cmO) .xmm0]))

/-- `vg_aes_encrypt_blocks`'s arguments: the encryption key's schedule, the
`r14` counter blocks at `W + revO` and the working space. -/
def ecbArgs : List Instr :=
  ptr .rdi .r15 skO ++ ([.mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 revO ++
    ([.mov .rcx (.reg .r14)] : List Instr) ++ ptr .r8 .r15 scrO

/-- The body of the keystream XOR: one keystream block at `rsi` XORed into
the data at `r12`; both on, and `rcx` one fewer. -/
def ksOne : List Instr :=
  [.movdquLoad .xmm0 (at_ .r12 0), .movdquLoad .xmm1 (at_ .rsi 0), .xop (.bin .pxor .xmm0 .xmm1),
    .movdquStore (at_ .r12 0) .xmm0, .alu .add .r12 (imm 16), .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)]

/-- Two keystream blocks at `rsi + d` XORed into the data at `r12 + d`. -/
def xor2 (d : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm1 (at_ .rsi d), .vmovdquLoad .l256 .xmm0 (at_ .r12 d),
    .vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm0), .vmovdquStore .l256 (at_ .r12 d) .xmm1]

/-- Four keystream blocks at `rsi` XORed into the data at `r12`; `rcx`
four fewer, compared with 4. -/
def ksQuad : List Instr :=
  xor2 0 ++ xor2 32 ++
    ([.alu .add .r12 (imm 64), .alu .add .rsi (imm 64), .alu .sub .rcx (imm 4), .alu .cmp .rcx (imm 4)] : List Instr)

/-- The loop of the keystream XOR: one block at a time, or, if `wide`, four
at a time on 256-bit registers while four are left. -/
def ksLoop (wide : Bool) : Prog isa :=
  if wide then quadsThenOnes [] ksQuad ksOne else .loop (.block ksOne) .ne

/-- The `r14` keystream blocks at `W + revO` XORed into the data at `r12`;
`r12` past them. -/
def ksXor (wide : Bool) : Prog isa :=
  .seq (.block (([.mov .rcx (.reg .r14)] : List Instr) ++ ptr .rsi .r15 revO)) (ksLoop wide)

/-- Up to 64 of the `rbx` whole blocks left at `r12` (`r14` of them)
encrypted: their counter blocks, encrypted by `vg_aes_encrypt_blocks` in
place, XORed into them; `rbx` fewer left (ZF set when none are). -/
def cryptChunk (wide : Bool) : Prog isa :=
  .seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
  (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
  (.seq ctrGen
  (.seq (.block ecbArgs)
  (.seq (callEcb e)
  (.seq (ksXor wide) (.block [.alu .sub .rbx (.reg .r14)]))))))

/-- The last `rbp` (1 to 15) bytes at `r12` XORed with the keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block (copy16 cmO ccO ++ zero16 bO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 bO))
  (.seq (callCtr c)
    (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop))

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt (wide : Bool) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
      .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
      .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
      .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (cryptChunk e wide) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (cryptTail c))))

/-! ## Comparing tags and masking -/

/-- `ok = 1` at `W + okO` if the tags at `W` and `W + bO` are equal, 0 if
not, without a branch. -/
def cmp : List Instr :=
  [.mov .rax (.mem (at_ .r15 tagO)), .alu .xor .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (tagO + 8))),
    .alu .xor .rdx (.mem (at_ .r15 (bO + 8))), .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1),
    .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0), .store (at_ .r15 okO) .rax]

/-- Every byte of the data ANDed with `0 − ok` (`maskTail`): its whole
blocks, then the rest. -/
def mask : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
      .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
      .shift .shr .rcx 4, .alu .test .rcx (.reg .rcx)])
    maskTail

/-! ## The functions -/

/-- Saves the registers in `W` (whose address, the ninth argument, is on
the stack above the length and `tag`, the seventh and eighth), keeps `W` in
`r15` and the key schedule in `r13`, and the other arguments but `tag` in
`W`. -/
def entry : List Instr :=
  ([.mov .rax (.mem (at_ .rsp 24)), .mov .r10 (.mem (at_ .rsp 8))] : List Instr) ++ save .rax ++
    ([.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 nonceO) .rdx,
      .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
      .store (at_ .r15 lenO) .r10] : List Instr)

/-- The received tag copied from `tag`, whose address is at `[rsp + 16]`, to
`W`. -/
def recv : List Instr :=
  [.mov .rcx (.mem (at_ .rsp 16)), .mov .rax (.mem (at_ .rcx 0)), .store (at_ .r15 tagO) .rax,
    .mov .rax (.mem (at_ .rcx 8)), .store (at_ .r15 (tagO + 8)) .rax]

/-- The tag copied from `W` to `tag`, whose address is at `[rsp + 16]`. -/
def tagOut : List Instr :=
  [.mov .rcx (.mem (at_ .rsp 16)), .mov .rax (.mem (at_ .r15 tagO)), .store (at_ .rcx 0) .rax,
    .mov .rax (.mem (at_ .r15 (tagO + 8))), .store (at_ .rcx 8) .rax]

/-- The keys and POLYVAL's key. -/
def keys : Prog isa :=
  .seq (derive e) (.seq (expand c) (.block hkey))

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input, absorbing up to 64 blocks per call of `vg_ghash`. -/
def polyvalLong (wide : Bool) : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))])
  (.seq (absorb c wide)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
  (.seq (absorb c wide)
  (.seq (lens c) (.block tagIn)))))

/-- The last `rbp` (1 to 15) bytes at `rsi`, padded with zeros, reversed at
`rdi`; `rdi` past them. -/
def stageTail : Prog isa :=
  .seq (.block (([.mov .rbx (.reg .rdi)] : List Instr) ++ zero16 bO ++ ptr .rdi .r15 bO ++
      ([.mov .rcx (.reg .rbp)] : List Instr)))
  (.seq copyLoop
    (.block [.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx,
      .store (at_ .rbx 0) .rdx, .store (at_ .rbx 8) .rax, .mov .rdi (.reg .rbx), .alu .add .rdi (imm 16)]))

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, reversed at
`rdi`; `rdi` past them. -/
def stage (wide : Bool) : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .mov .rsi (.reg .r12),
      .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.seq (.block [.mov .r14 (.reg .rbx)]) (revSel wide)))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) stageTail)))

/-- The lengths block at `rdi`, in GHASH's order, and `vg_ghash`'s arguments
for the blocks from `W + revO` to it. -/
def lensAt : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .rdi 0) .rax,
    .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .rdi 8) .rax,
    .mov .rcx (.reg .rdi), .alu .sub .rcx (.reg .r15), .shift .shr .rcx 4, .alu .sub .rcx (imm (revO / 16 - 1))] ++
  ghArgs ++ ptr .rdx .r15 revO

/-- POLYVAL with one call of `vg_ghash`: the padded additional data, the
padded data and the lengths block, all reversed from `W + revO` first. -/
def polyvalOne (wide : Bool) : Prog isa :=
  .seq (.block (ptr .rdi .r15 revO ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] :
      List Instr)))
  (.seq (stage wide)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
  (.seq (stage wide)
  (.seq (.block lensAt)
  (.seq (callGh c) (.block tagIn))))))

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input: with one call of `vg_ghash` if their blocks fit the 64 at `W + revO`
(the whole blocks number at most 61), else `polyvalLong`. -/
def polyval (wide : Bool) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 alenO)), .shift .shr .rax 4, .mov .rdx (.mem (at_ .r15 lenO)),
      .shift .shr .rdx 4, .alu .add .rax (.reg .rdx), .alu .cmp .rax (imm 62)])
    (.ite .ae (polyvalLong c wide) (polyvalOne c wide))

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» (wide : Bool) : Prog isa :=
  .seq (.block entry) (.seq (keys c e) (.seq (polyval c wide) (.seq (tag c tagO) (.seq (crypt c e wide)
    (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» (wide : Bool) : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq (keys c e) (.seq (crypt c e wide) (.seq (polyval c wide) (.seq (tag c bO)
    (.seq (.block cmp) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))

end VG.Impl.AesGcmSiv.X86_64
