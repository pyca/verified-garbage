import VerifiedGarbage.Impl.AesGcm.X86_64

/-!
# AES-GCM-SIV: x86-64 implementation

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Spec/GcmSiv/Contract.lean`),
composed of calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`, and generic over their implementations as AES-GCM is
(`Impl.AesGcm.X86_64.Callees`: only `ctr`, `key` and `gh` are called).

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  by `vg_aes_expand_key`, for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: each block is
  copied to `W + 768` with its bytes reversed before `vg_ghash` absorbs it
  (`absorb`), up to 64 at a time; the lengths block is written in GHASH's
  order (`lens`), and the result is read back reversed (`tagIn`).
* The tag is `vg_aes_ctr32` of the tag input on a zero block (`tag`).
* Counter mode (§4) increments the first 4 bytes of the counter block, as a
  little-endian number, which `vg_aes_ctr32` (which increments the last 4,
  big-endian) does not: each block is encrypted by a call of its own from a
  copy of the counter block, which is then incremented (`crypt`).
* `open` decrypts first, computes the tag of the plaintext at `W + 144` and
  compares it with the received one without a branch (`cmp`), then masks
  the data with `0 − ok` (`mask`).

## The working space `W` (4096 bytes)

* `[0, 16)`: the tag; `[16, 32)`: the authentication key; `[32, 64)`: the
  encryption key; `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator;
  `[96, 112)`: the counter block (or the tag input); `[112, 128)`: a copy of
  it for a call; `[128, 144)`: a block; `[144, 160)`: the tag `open`
  computes; `[160, 208)`: our caller's `rbx, rbp, r12–r15`; `[208, 216)`:
  `ok`; `[272, 320)`: the public arguments;
* `[512, 752)`: the encryption key's schedule; `[768, 1792)`: the reversed
  blocks; `[1792, 2048)`: `vg_ghash`'s working space; `[2048, 4096)`:
  `vg_aes_ctr32`'s, and `vg_aes_expand_key`'s at its start.

`r15` holds `W` and `r13` the key schedule throughout; the functions called
preserve them, and `rbx`, `rbp`, `r12` and `r14`, which hold lengths,
pointers and counts across calls. Only the pointers, the lengths and
`rounds` (and for `open`, whether the tag is right) affect timing.
-/

namespace VG.Impl.AesGcmSiv.X86_64

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop xorLoop Callees)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cmO : Nat := 96
def ccO : Nat := 112
def bO : Nat := 128
def t2O : Nat := 144
def okO : Nat := 208
def roundsO : Nat := 272
def nonceO : Nat := 280
def aadO : Nat := 288
def alenO : Nat := 296
def dataO : Nat := 304
def lenO : Nat := 312
def skO : Nat := 512
def revO : Nat := 768
def ghO : Nat := 1792
def scrO : Nat := 2048

/-- Where our caller's callee-saved registers are kept. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 160), (.rbp, 168), (.r12, 176), (.r13, 184), (.r14, 192), (.r15, 200)]

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

/-- `vg_aes_ctr32`'s arguments but the key schedule: one block at `rcx`, the
counter block at `W + ccO` and the working space. -/
def ctrArgs : List Instr :=
  [.mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 ccO ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO

/-! ## The keys -/

/-- `little_endian_uint32(rbx) ‖ nonce` at `W + ccO`, and a zero block at
`W + bO`. -/
def deriveBlock : List Instr :=
  [.store32 (at_ .r15 ccO) .rbx, .mov .rax (.mem (at_ .r15 nonceO)), .mov .rcx (.mem (at_ .rax 0)),
    .store (at_ .r15 (ccO + 4)) .rcx, .mov32 .rcx (.mem (at_ .rax 8)), .store32 (at_ .r15 (ccO + 12)) .rcx] ++
  zero16 bO

/-- The message keys, 8 bytes per block, from `W + akO`. -/
def derive : Prog isa :=
  .seq (.block ([.mov32 .rbx (imm 0)] ++ ptr .r12 .r15 akO ++
      [.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)]))
    (.loop (.seq (.block (deriveBlock ++ [.mov .rdi (.reg .r13)] ++ ctrArgs ++ ptr .rcx .r15 bO))
      (.seq (callCtr c)
        (.block [.mov .rax (.mem (at_ .r15 bO)), .store (at_ .r12 0) .rax, .alu .add .r12 (imm 8),
          .alu .add .rbx (imm 1), .alu .cmp .rbx (.reg .rbp)]))) .ne)

/-- The encryption key's schedule at `W + skO`: its length is
`4 (rounds − 6)`. -/
def expand : Prog isa :=
  .seq (.block (ptr .rdi .r15 ekO ++ [.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO))
    (callKey c)

/-- GHASH's key, `H · x` for the authentication key `H` (as a
little-endian number), in GHASH's order at `W + hO`, and its accumulator
zeroed. -/
def hkey : List Instr :=
  [.mov .rax (.mem (at_ .r15 akO)), .mov .rdx (.mem (at_ .r15 (akO + 8))), .mov .rcx (.reg .rax),
    .alu .and .rcx (imm 1), .mov32 .r8 (imm 0), .alu .sub .r8 (.reg .rcx), .shift .shr .rax 1,
    .mov .rcx (.reg .rdx), .alu .and .rcx (imm 1), .shift .ror .rcx 1, .alu .or .rax (.reg .rcx), .shift .shr .rdx 1,
    .movImm64 .rcx 0xE100000000000000, .alu .and .rcx (.reg .r8), .alu .xor .rdx (.reg .rcx), .bswap .rdx,
    .bswap .rax, .store (at_ .r15 hO) .rdx, .store (at_ .r15 (hO + 8)) .rax] ++ zero16 yO

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

/-- Up to 64 of the `rbx` whole blocks at `r12` (`r14` of them), reversed and
absorbed; `r12` and `rbx` past them. -/
def absorbChunk : Prog isa :=
  .seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
  (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
  (.seq (.block ([.mov .rsi (.reg .r12)] ++ ptr .rdi .r15 revO))
  (.seq revLoop
  (.seq (.block (ghArgs ++ ptr .rdx .r15 revO ++ [.mov .rcx (.reg .r14)]))
  (.seq (callGh c)
    (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)]))))))

/-- The last `rbp` (1 to 15) bytes at `r12`, padded with zeros, reversed and
absorbed. -/
def absorbTail : Prog isa :=
  .seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ [.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)]))
  (.seq copyLoop
  (.seq (.block ([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx,
      .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] ++ ghArgs ++ ptr .rdx .r15 revO ++
      [.mov32 .rcx (imm 1)]))
    (callGh c)))

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (absorbChunk c) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (absorbTail c))))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, in GHASH's order
at `W + bO`, absorbed. -/
def lens : Prog isa :=
  .seq (.block ([.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 bO) .rax,
      .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] ++
      ghArgs ++ ptr .rdx .r15 bO ++ [.mov32 .rcx (imm 1)]))
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

/-- One block at `r12` encrypted from the counter block, which is then
incremented; `r12` past it. -/
def cryptBlock : Prog isa :=
  .seq (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ [.mov .rcx (.reg .r12)]))
  (.seq (callCtr c)
    (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
      .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]))

/-- The last `rbp` (1 to 15) bytes at `r12` XORed with the keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block (copy16 cmO ccO ++ zero16 bO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 bO))
  (.seq (callCtr c)
    (.seq (.block ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r15 bO ++ [.mov .rcx (.reg .rbp)])) xorLoop))

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
      .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
      .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
      .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (cryptBlock c) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (cryptTail c))))

/-! ## Comparing tags and masking -/

/-- `ok = 1` at `W + okO` if the tags at `W` and `W + t2O` are equal, 0 if
not, without a branch. -/
def cmp : List Instr :=
  [.mov .rax (.mem (at_ .r15 tagO)), .alu .xor .rax (.mem (at_ .r15 t2O)), .mov .rdx (.mem (at_ .r15 (tagO + 8))),
    .alu .xor .rdx (.mem (at_ .r15 (t2O + 8))), .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1),
    .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0), .store (at_ .r15 okO) .rax]

def maskByte : MemOp := { base := .r12, index := some .r10 }

/-- Every byte of the data ANDed with `0 − ok`. -/
def mask : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
      .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rbp)]) .ne))

/-! ## The functions -/

/-- Saves the registers in `W` (whose address, the eighth argument, is on
the stack above the length, the seventh), keeps `W` in `r15` and the key
schedule in `r13`, and the other arguments in `W`. -/
def entry : List Instr :=
  [.mov .rax (.mem (at_ .rsp 16)), .mov .r10 (.mem (at_ .rsp 8))] ++ save .rax ++
    [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 nonceO) .rdx,
      .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8, .store (at_ .r15 dataO) .r9,
      .store (at_ .r15 lenO) .r10]

/-- The keys and POLYVAL's key. -/
def keys : Prog isa :=
  .seq (derive c) (.seq (expand c) (.block hkey))

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))])
  (.seq (absorb c)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
  (.seq (absorb c)
  (.seq (lens c) (.block tagIn)))))

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq (keys c) (.seq (polyval c) (.seq (tag c tagO) (.seq (crypt c) (.block restore)))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (keys c) (.seq (crypt c) (.seq (polyval c) (.seq (tag c t2O)
    (.seq (.block cmp) (.seq mask (.block ([.mov .rax (.mem (at_ .r15 okO))] ++ restore))))))))

end VG.Impl.AesGcmSiv.X86_64
