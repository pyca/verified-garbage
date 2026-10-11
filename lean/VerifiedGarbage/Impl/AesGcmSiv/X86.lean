module

public import VerifiedGarbage.Impl.AesGcm.X86

/-!
# AES-GCM-SIV: x86 (32-bit) implementation

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Spec/GcmSiv/Contract.lean`),
cdecl (every argument on the stack), composed of calls of the verified
`vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`, and generic over their
implementations as AES-GCM is (`Impl.AesGcm.X86.Callees`). The algorithm is
ARMv7's (`Impl/AesGcmSiv/Arm.lean`), on 32-bit words; the conventions are
x86's AES-GCM's (`Impl/AesGcm/X86.lean`):

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  by `vg_aes_expand_key`, for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: up to 64 blocks
  at a time are copied to `W + 768` with their bytes reversed before
  `vg_ghash` absorbs them (`chunk`). The last bytes of a string, padded
  with zeros, and the lengths block are put in the block at `W + 224` and
  absorbed the same way (`absorb`, `lens`); the result is read back
  reversed (`tagIn`).
* The tag is `vg_aes_ctr32` of the tag input on a zero block (`tag`).
* Counter mode (§4) increments the first 4 bytes of the counter block, as a
  little-endian number, which `vg_aes_ctr32` (which increments the last 4,
  big-endian) does not: each block is encrypted by a call of its own from a
  copy of the counter block, which is then incremented (`cryptBlock`); the
  last bytes are XORed with a keystream block computed as a tag is
  (`cryptTail`).
* `open` decrypts first, computes the tag of the plaintext at `W + 240` and
  compares it with the received one without a branch (`cmp`), then ANDs
  every byte of the data with `0 − ok` (`mask`).

The model has no left shift: `x << 31` is `ror (x & 1), 1` and `x << 3`
three additions.

## The working space `W` (2816 bytes)

`work` is the ninth argument, which the frame of the artifacts allocates on
the stack (`Proof/AesGcmSiv/X86/Frame.lean`).

* `[0, 16)`: the tag (`seal` copies it out to `tag` at the end, `open` copies
  the received one in at the start); `[16, 32)`: the authentication key;
  `[32, 64)`: the encryption key; `[64, 80)`: GHASH's key; `[80, 96)`: its
  accumulator; `[96, 112)`: the counter block (or the tag input);
  `[112, 128)`: a copy of it for a call; `[128, 144)`: our caller's `ebx`,
  `esi`, `edi`, `ebp`; `[144, 176)`: the arguments but `work`, kept
  (`ctxO` … `tpO`); `[176, 184)`: the variables of the pieces (`nO`,
  `iO`); `[224, 240)`: a block; `[240, 256)`: the tag `open` computes;
* `[512, 752)`: the encryption key's schedule; `[768, 1792)`: the reversed
  blocks; `[1792, 2048)`: `vg_ghash`'s working space; `[768, 2816)`:
  `vg_aes_ctr32`'s, and `vg_aes_expand_key`'s at its start, over the last
  two, which are used only within POLYVAL, which calls neither.

## Registers

`ebp` holds `W` throughout; the functions called preserve it. The pieces
on a string keep their pointer in `esi`, which the functions called also
preserve, and the number of bytes left at `W + nO`. Everything else is
reloaded from `W`. Each call pushes its arguments in a frame of its own
(AES-GCM's `ctrCall`, `ghCall`, `keyCall`): `vg_aes_ctr32` six,
`vg_ghash` five and `vg_aes_expand_key` four, with the return address 28
bytes of stack at most. The callee's working space is passed in `ebp`,
moved there before the frame and back after it.

Only the pointers, the lengths and `rounds` (and for `open`, whether the tag
is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86

open VG.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry restore zero4 copyLoop xorLoop Callees ctrCall ghCall
  keyCall)

abbrev tagO : Nat := 0
abbrev akO : Nat := 16
abbrev ekO : Nat := 32
abbrev hO : Nat := 64
abbrev yO : Nat := 80
abbrev cbO : Nat := 96
abbrev ccO : Nat := 112
abbrev ctxO : Nat := 144
abbrev roundsO : Nat := 148
abbrev nonceO : Nat := 152
abbrev aadO : Nat := 156
abbrev alenO : Nat := 160
abbrev dataO : Nat := 164
abbrev lenO : Nat := 168
/-- The pointer to the tag. -/
abbrev tpO : Nat := 172
/-- The number of bytes left of the string a piece is on. -/
abbrev nO : Nat := 176
/-- A count: the message key `derive` is on, or the blocks of a chunk. -/
abbrev iO : Nat := 180
abbrev bO : Nat := 224
abbrev t2O : Nat := 240
abbrev skO : Nat := 512
abbrev revO : Nat := 768
abbrev ghO : Nat := 1792
abbrev scrO : Nat := 768

/-- The 16 bytes at `W + s` copied to `W + d`. -/
def copy16 (s d : Nat) : List Instr :=
  [.mov .eax (slot s), .store (at_ .ebp d) .eax, .mov .eax (slot (s + 4)), .store (at_ .ebp (d + 4)) .eax,
   .mov .eax (slot (s + 8)), .store (at_ .ebp (d + 8)) .eax, .mov .eax (slot (s + 12)),
   .store (at_ .ebp (d + 12)) .eax]

section
variable (c : Callees)

/-- `vg_aes_ctr32`, with the working space at `W + 768`. -/
def callCtr : Prog isa :=
  .seq (.block [.alu .add .ebp (imm scrO)]) (.seq (ctrCall c) (.block [.alu .sub .ebp (imm scrO)]))

/-- `vg_ghash`, with the working space at `W + 1792`. -/
def callGh : Prog isa :=
  .seq (.block [.alu .add .ebp (imm ghO)]) (.seq (ghCall c) (.block [.alu .sub .ebp (imm ghO)]))

/-- `vg_aes_expand_key`, with the working space at `W + 2048`. -/
def callKey : Prog isa :=
  .seq (.block [.alu .add .ebp (imm scrO)]) (.seq (keyCall c) (.block [.alu .sub .ebp (imm scrO)]))

/-- The arguments of `vg_aes_ctr32` for one block at `W + o`: the
encryption key's schedule, the rounds and the copy of the counter block at
`W + 112`. -/
def ctrArgs (o : Nat) : List Instr :=
  [.mov .eax (.reg .ebp), .alu .add .eax (imm skO), .mov .ecx (slot roundsO), .mov .edx (.reg .ebp),
   .alu .add .edx (imm ccO), .mov .ebx (.reg .ebp), .alu .add .ebx (imm o), .mov .edi (imm 1)]

/-! ## The keys -/

/-- `little_endian_uint32(i) ‖ nonce` at `W + 112` (the nonce loaded
first), a zero block at `W + 224`, and the arguments of `vg_aes_ctr32` with
the key-generating key's schedule. -/
def deriveBlock : List Instr :=
  ([.mov .eax (slot nonceO), .mov .ecx (.mem (at_ .eax 0)), .mov .edx (.mem (at_ .eax 4)),
   .mov .ebx (.mem (at_ .eax 8)), .store (at_ .ebp (ccO + 4)) .ecx, .store (at_ .ebp (ccO + 8)) .edx,
   .store (at_ .ebp (ccO + 12)) .ebx, .mov .eax (slot iO), .store (at_ .ebp ccO) .eax] : List Instr) ++ zero4 bO ++
    ([.mov .eax (slot ctxO), .mov .ecx (slot roundsO), .mov .edx (.reg .ebp), .alu .add .edx (imm ccO),
     .mov .ebx (.reg .ebp), .alu .add .ebx (imm bO), .mov .edi (imm 1)] : List Instr)

/-- The first 8 bytes of the block kept at `W + 16 + 8 i`, the next `i`,
and ZF set after the last block (`rounds / 2 - 1` of them). -/
def derivePost : List Instr :=
  [.mov .edx (slot iO), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
   .alu .add .edx (.reg .ebp), .mov .eax (slot bO), .store (at_ .edx akO) .eax, .mov .eax (slot (bO + 4)),
   .store (at_ .edx (akO + 4)) .eax, .mov .eax (slot iO), .alu .add .eax (imm 1), .store (at_ .ebp iO) .eax,
   .mov .ecx (slot roundsO), .shift .shr .ecx 1, .alu .sub .ecx (imm 1), .alu .cmp .eax (.reg .ecx)]

/-- The message keys, 8 bytes per block, from `W + 16`. -/
def derive : Prog isa :=
  .seq (.block [.mov .eax (imm 0), .store (at_ .ebp iO) .eax])
    (.loop (.seq (.block deriveBlock) (.seq (callCtr c) (.block derivePost))) .ne)

/-- The arguments of `vg_aes_expand_key`: the encryption key, whose length
is `4 (rounds − 6)`, and its schedule at `W + 512`. -/
def expandArgs : List Instr :=
  [.mov .eax (.reg .ebp), .alu .add .eax (imm ekO), .mov .ecx (slot roundsO), .alu .sub .ecx (imm 6),
   .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .mov .edx (.reg .ebp), .alu .add .edx (imm skO)]

/-- The encryption key's schedule at `W + 512`. -/
def expand : Prog isa := .seq (.block expandArgs) (callKey c)

/-- Word `k` (0 to 2) of `H · x`, `(w_k >> 1) | (w_{k+1} << 31)` for the
words `w` of the authentication key, reversed into word `3 − k` of GHASH's
key. -/
def hkeyW (k : Nat) : List Instr :=
  [.mov .eax (slot (akO + 4 * k)), .shift .shr .eax 1, .mov .ecx (slot (akO + 4 * k + 4)), .alu .and .ecx (imm 1),
   .shift .ror .ecx 1, .alu .or .eax (.reg .ecx), .bswap .eax, .store (at_ .ebp (hO + 12 - 4 * k)) .eax]

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number), in GHASH's order at `W + 64`, and its accumulator zeroed. -/
def hkey : List Instr :=
  hkeyW 0 ++ hkeyW 1 ++ hkeyW 2 ++
    ([.mov .eax (slot (akO + 12)), .shift .shr .eax 1, .mov .ecx (slot akO), .alu .and .ecx (imm 1),
     .mov .edx (imm 0), .alu .sub .edx (.reg .ecx), .alu .and .edx (imm 0xE1000000), .alu .xor .eax (.reg .edx),
     .bswap .eax, .store (at_ .ebp hO) .eax] : List Instr) ++ zero4 yO

/-- The keys and GHASH's key. -/
def keys : Prog isa := .seq (derive c) (.seq (expand c) (.block hkey))

/-! ## POLYVAL -/

/-- `ecx := min (nO / 16, 64)`, kept at `W + iO`. -/
def chunkLen : Prog isa :=
  .seq (.block [.mov .ecx (slot nO), .shift .shr .ecx 4, .alu .cmp .ecx (imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov .ecx (imm 64)])) (.block [.store (at_ .ebp iO) .ecx]))

/-- The `ecx` (at least 1) blocks at `esi` copied to `edx`, the bytes of
each reversed, advancing both. -/
def revLoop : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .esi 12)), .bswap .eax, .store (at_ .edx 0) .eax,
    .mov .eax (.mem (at_ .esi 8)), .bswap .eax, .store (at_ .edx 4) .eax, .mov .eax (.mem (at_ .esi 4)),
    .bswap .eax, .store (at_ .edx 8) .eax, .mov .eax (.mem (at_ .esi 0)), .bswap .eax, .store (at_ .edx 12) .eax,
    .alu .add .esi (imm 16), .alu .add .edx (imm 16), .alu .sub .ecx (imm 1)]) .ne

/-- After the copies: `W + nO` past the blocks, and the arguments of
`vg_ghash`. -/
def chunkArgs : List Instr :=
  [.mov .edi (slot iO), .mov .eax (.reg .edi), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .ecx (slot nO), .alu .sub .ecx (.reg .eax),
   .store (at_ .ebp nO) .ecx, .mov .eax (.reg .ebp), .alu .add .eax (imm hO), .mov .edx (.reg .ebp),
   .alu .add .edx (imm yO), .mov .ebx (.reg .ebp), .alu .add .ebx (imm revO)]

/-- Up to 64 of the whole blocks of the `nO` bytes at `esi` reversed at
`W + 768`, `esi` and `nO` past them, and the arguments of `vg_ghash`. -/
def chunkPre : Prog isa :=
  .seq (chunkLen) (.seq (.block [.mov .edx (.reg .ebp), .alu .add .edx (imm revO)]) (.seq revLoop (.block chunkArgs)))

/-- ZF set iff fewer than 16 of the `nO` bytes are left. -/
def wholeLeft : List Instr := [.mov .ecx (slot nO), .shift .shr .ecx 4, .alu .test .ecx (.reg .ecx)]

/-- Up to 64 of the whole blocks of the `nO` bytes at `esi`, reversed and
absorbed; `esi` and `nO` past them, and ZF set if no whole block is left. -/
def chunk : Prog isa := .seq (chunkPre) (.seq (callGh c) (.block wholeLeft))

/-- ZF set iff no byte is left. -/
def anyLeft : List Instr := [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)]

/-- The last `nO` (1 to 15) bytes at `esi`, padded with zeros at
`W + 224`, as the 16 bytes to absorb. -/
def absTailPre : Prog isa :=
  .seq (.block (zero4 bO ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm bO),
      .mov .ecx (slot nO)] : List Instr)))
    (.seq copyLoop (.block [.mov .esi (.reg .ebp), .alu .add .esi (imm bO), .mov .eax (imm 16),
      .store (at_ .ebp nO) .eax]))

/-- The last `nO` (1 to 15) bytes at `esi`, padded with zeros at
`W + 224`, absorbed. -/
def absTail : Prog isa := .seq absTailPre (chunk c)

/-- The `nO` bytes at `esi`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block wholeLeft)
  (.seq (.ite .e (.block []) (.loop (chunk c) .ne))
  (.seq (.block anyLeft) (.ite .e (.block []) (absTail c))))

/-- `little_endian_uint64(8 x)` at `W + o`, for the 32-bit `x` at `W + s`. -/
def le64At (s o : Nat) : List Instr :=
  [.mov .eax (slot s), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .store (at_ .ebp o) .eax, .mov .eax (slot s), .shift .shr .eax 29, .store (at_ .ebp (o + 4)) .eax]

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, at `W + 224`, as
the 16 bytes to absorb. -/
def lensBlock : List Instr :=
  le64At alenO bO ++ le64At lenO (bO + 8) ++
    ([.mov .esi (.reg .ebp), .alu .add .esi (imm bO), .mov .eax (imm 16), .store (at_ .ebp nO) .eax] : List Instr)

/-- The lengths block absorbed. -/
def lens : Prog isa := .seq (.block lensBlock) (chunk c)

/-- Word `k` (0 to 2) of the tag input: word `3 − k` of the accumulator,
reversed, XORed with word `k` of the nonce (in `r`). -/
def tagInW (k : Nat) (r : Reg) : List Instr :=
  [.mov .eax (slot (yO + 12 - 4 * k)), .bswap .eax, .alu .xor .eax (.reg r), .store (at_ .ebp (cbO + 4 * k)) .eax]

/-- The tag input at `W + 96`: POLYVAL's result in its own order (the words
of the accumulator in the other order, each reversed), its first 12 bytes
XORed with the nonce (loaded first) and the top bit of its last byte
cleared. -/
def tagIn : List Instr :=
  ([.mov .ecx (slot nonceO), .mov .edx (.mem (at_ .ecx 0)), .mov .ebx (.mem (at_ .ecx 4)),
   .mov .edi (.mem (at_ .ecx 8))] : List Instr) ++ tagInW 0 .edx ++ tagInW 1 .ebx ++ tagInW 2 .edi ++
    ([.mov .eax (slot yO), .bswap .eax, .alu .and .eax (imm 0x7FFFFFFF), .store (at_ .ebp (cbO + 12)) .eax] : List Instr)

/-- The string at `W + s` (`W + l` bytes) as the bytes to absorb. -/
def onStr (s l : Nat) : List Instr := [.mov .esi (slot s), .mov .eax (slot l), .store (at_ .ebp nO) .eax]

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block (onStr aadO alenO))
  (.seq (absorb c)
  (.seq (.block (onStr dataO lenO))
  (.seq (absorb c)
  (.seq (lens c) (.block tagIn)))))

/-- The encryption of the block at `W + 96` with the encryption key, at
`W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ zero4 o ++ ctrArgs o)) (callCtr c)

/-! ## Counter mode -/

/-- The counter block from the tag at `W`, with the top bit of its last
byte set, and the data as the bytes to encrypt; ZF set if it has no whole
block. -/
def cryptHead : List Instr :=
  ([.mov .eax (slot tagO), .store (at_ .ebp cbO) .eax, .mov .eax (slot (tagO + 4)), .store (at_ .ebp (cbO + 4)) .eax,
   .mov .eax (slot (tagO + 8)), .store (at_ .ebp (cbO + 8)) .eax, .mov .eax (slot (tagO + 12)),
   .alu .or .eax (imm 0x80000000), .store (at_ .ebp (cbO + 12)) .eax] : List Instr) ++ onStr dataO lenO ++ wholeLeft

/-- The arguments of `vg_aes_ctr32` for the block at `esi`. -/
def blockArgs : List Instr :=
  copy16 cbO ccO ++ ([.mov .eax (.reg .ebp), .alu .add .eax (imm skO), .mov .ecx (slot roundsO),
    .mov .edx (.reg .ebp), .alu .add .edx (imm ccO), .mov .ebx (.reg .esi), .mov .edi (imm 1)] : List Instr)

/-- After a block: the counter block's first word incremented, `esi` and
`nO` past the block, and ZF set if no whole block is left. -/
def blockNext : List Instr :=
  ([.mov .eax (slot cbO), .alu .add .eax (imm 1), .store (at_ .ebp cbO) .eax, .alu .add .esi (imm 16),
   .mov .eax (slot nO), .alu .sub .eax (imm 16), .store (at_ .ebp nO) .eax] : List Instr) ++ wholeLeft

/-- One block at `esi` encrypted in place from the counter block, which is
then incremented; `esi` and `nO` past it, and ZF set if no whole block is
left. -/
def cryptBlock : Prog isa := .seq (.block blockArgs) (.seq (callCtr c) (.block blockNext))

/-- The last `nO` (1 to 15) bytes at `esi` XORed with a keystream block,
computed at `W + 224`. -/
def cryptTail : Prog isa :=
  .seq (tag c bO) (.seq (.block [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi),
    .mov .ecx (slot nO)]) xorLoop)

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (.ite .e (.block []) (.loop (cryptBlock c) .ne))
  (.seq (.block anyLeft) (.ite .e (.block []) (cryptTail c))))

end

/-! ## Comparing tags and masking -/

/-- `eax = 1` if the tags at `W` and `W + 240` are equal, 0 if not, without
a branch (AES-GCM's `cmpTail`). -/
def cmp : List Instr :=
  [.mov .eax (slot tagO), .alu .xor .eax (slot t2O), .mov .ecx (slot (tagO + 4)), .alu .xor .ecx (slot (t2O + 4)),
   .alu .or .eax (.reg .ecx), .mov .ecx (slot (tagO + 8)), .alu .xor .ecx (slot (t2O + 8)),
   .alu .or .eax (.reg .ecx), .mov .ecx (slot (tagO + 12)), .alu .xor .ecx (slot (t2O + 12)),
   .alu .or .eax (.reg .ecx), .alu .cmp .eax (imm 1), .mov .eax (imm 0), .alu .adc .eax (imm 0)]

/-- Every byte of the data ANDed with `0 − eax`, with `eax` kept. -/
def mask : Prog isa :=
  .seq (.block [.mov .ebx (imm 0), .alu .sub .ebx (.reg .eax), .mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .edi (slot dataO)])
        (.loop (.block [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl,
          .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne)))

/-! ## The functions -/

/-- Our caller's registers saved in `work` (the ninth argument), `ebp :=`
`work`, and the other arguments kept. -/
def sivEntry : Prog isa :=
  entry 8 (keep 0 ctxO ++ keep 1 roundsO ++ keep 2 nonceO ++ keep 3 aadO ++ keep 4 alenO ++ keep 5 dataO ++
    keep 6 lenO ++ keep 7 tpO)

/-- The received tag copied to `W`. -/
def recvTag : Prog isa :=
  .seq (.block [.mov .edi (slot tpO)])
    (.block [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
      .mov .ebx (.mem (at_ .edi 12)), .store (at_ .ebp tagO) .eax, .store (at_ .ebp (tagO + 4)) .ecx,
      .store (at_ .ebp (tagO + 8)) .edx, .store (at_ .ebp (tagO + 12)) .ebx])

/-- The tag at `W` copied out. -/
def tagOut : Prog isa :=
  .seq (.block [.mov .eax (slot tagO), .mov .ecx (slot (tagO + 4)), .mov .edx (slot (tagO + 8)),
      .mov .ebx (slot (tagO + 12)), .mov .edi (slot tpO)])
    (.block [.store (at_ .edi 0) .eax, .store (at_ .edi 4) .ecx, .store (at_ .edi 8) .edx,
      .store (at_ .edi 12) .ebx])

section
variable (c : Callees)

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq sivEntry (.seq (keys c) (.seq (polyval c) (.seq (tag c tagO) (.seq (crypt c) (.seq tagOut
    (.block restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq sivEntry (.seq recvTag (.seq (keys c) (.seq (crypt c) (.seq (polyval c) (.seq (tag c t2O)
    (.seq (.block cmp) (.seq mask (.block restore))))))))

end

end VG.Impl.AesGcmSiv.X86
