module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch

/-!
# AES-GCM-SIV with AES-NI and PCLMULQDQ: the keys, POLYVAL and the counters in registers

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` as `Impl/AesGcmSiv/X86_64.lean`
has them (the same arguments, entry, exit, comparison of the tags and
masking, and the same places in the working space `W` for what they keep
there), for CPUs with AES-NI, PCLMULQDQ and SSSE3, with no calls: what that
code passes between the functions it calls through `W` (the message keys'
blocks, POLYVAL's key and accumulator, the reversed blocks, the counter
blocks and the keystream) stays in registers here, and `W` ends with the
encryption key's schedule: 744 bytes.

* The message keys (RFC 8452 §4): the blocks
  `little_endian_uint32(i) ‖ nonce` are encrypted two at a time
  (`Impl.Aes.X86_64.AesNi.aes`), and the first 8 bytes of each pair stored
  with one 16-byte store, from `W + 16` (`derive`).
* The encryption key's schedule at `W + 248`: `AesNi.expandKey`, inline
  (`expand`).
* POLYVAL (§3) is GHASH on the same bits with the key `H · x` on blocks in
  the other byte order (`Proof.GcmSiv.Polyval`): GHASH's registers
  (`Impl.Gcm.X86_64.Pclmul`) hold each block as loaded, with no byte
  reversal, and `Y` as POLYVAL's result. The additional data is absorbed a
  block at a time, the data four blocks at a time with `H'`–`H'⁴` and then
  one at a time; a last partial block is copied to `W + 128`, padded with
  zeros (`absorb`); the lengths block is built in registers (`lens`).
* The tag is the encryption of the tag input, built in registers (`tagIn`),
  stored at `W + o` (`tag`).
* Counter mode (§4) increments the first 32-bit word of the counter block:
  `paddd` on the block as it is, four blocks at a time and then one at a
  time, XORed into the data in place; the last bytes are XORed with a
  keystream block at `W + 128` (`crypt`).

## Registers

`r15` holds `W` and `r13` the key-generating key's schedule throughout, as
in `Impl/AesGcmSiv/X86_64.lean`. `rdi`, `rsi` and `r10` are the schedule,
`rounds` and the last round key's address for `aes`; `r12` the bytes being
absorbed or enciphered, `rbx` a count of blocks, `rbp` a length; `rax`,
`rcx`, `rdx` and `r11` temporaries. `xmm1`–`xmm11` are GHASH's (`Pclmul`);
counter mode uses `xmm0`–`xmm3` for the blocks, `xmm8` for the round key,
`xmm9` for the counter block and `xmm10` for its increment.

Only the pointers, the lengths and `rounds` (and for `open`, whether the tag
is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64Reg

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop xorLoop)
open VG.Impl.Aes.X86_64.AesNi (aes expandKey)
open VG.Impl.Gcm.X86_64.Pclmul (zero acc reduce pows poly constImm hInvImm)
open VG.Impl.AesGcmSiv.X86_64 (tagO akO ekO bO okO roundsO nonceO aadO alenO dataO lenO skO entry recv tagOut
  restore cmp mask)

/-- The size of the working space. -/
def workLen : Nat := 744

/-- The last round key's address for `aes`, from the schedule in `rdi` and
`rounds` in `rsi`. -/
def lastKey : List Instr := [.mov .r10 (.reg .rsi), .shift .shl .r10 4, .alu .add .r10 (.reg .rdi)]

/-- `aes`'s arguments for the key whose schedule is at `r`. -/
def aesArgs (r : List Instr) : List Instr :=
  r ++ ([.mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ lastKey

/-! ## The keys -/

/-- The blocks `little_endian_uint32(rbx) ‖ nonce` and
`little_endian_uint32(rbx + 1) ‖ nonce` in `xmm0` and `xmm1` (`rbx` even,
below 6; the nonce at `rdx`). -/
def derivePair : List Instr :=
  [.mov .rax (.mem (at_ .rdx 4)), .xop (.movq .xmm2 .rax),
   .mov32 .rax (.mem (at_ .rdx 0)), .shift .shl .rax 32, .alu .or .rax (.reg .rbx),
   .xop (.movq .xmm0 .rax), .xop (.bin .punpcklqdq .xmm0 .xmm2),
   .alu .or .rax (imm 1), .xop (.movq .xmm1 .rax), .xop (.bin .punpcklqdq .xmm1 .xmm2)]

/-- The first 8 bytes of `xmm0` and of `xmm1` at `W + akO + 8 · rbx`, with
one 16-byte store; `rbx` two more, compared with `rounds / 2 − 1`. -/
def deriveKeep : List Instr :=
  [.xop (.bin .punpcklqdq .xmm0 .xmm1),
   .mov .rax (.reg .rbx), .shift .shl .rax 3, .alu .add .rax (.reg .r15),
   .movdquStore (at_ .rax akO) .xmm0,
   .alu .add .rbx (imm 2), .mov .rax (.reg .rsi), .shift .shr .rax 1, .alu .sub .rax (imm 1),
   .alu .cmp .rbx (.reg .rax)]

/-- The message keys, 8 bytes per block, from `W + akO`. -/
def derive : Prog isa :=
  .seq (.block (aesArgs [.mov .rdi (.reg .r13)] ++
      ([.mov .rdx (.mem (at_ .r15 nonceO)), .mov32 .rbx (imm 0)] : List Instr)))
    (.loop (.seq (.block derivePair) (.seq (aes [.xmm0, .xmm1]) (.block deriveKeep))) .ne)

/-- The encryption key's schedule at `W + skO`: its length is
`4 (rounds − 6)`. -/
def expand : Prog isa :=
  .seq (.block (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO))
    expandKey

/-- The keys: the message keys, and the encryption key's schedule. -/
def keys : Prog isa := .seq derive expand

/-! ## POLYVAL -/

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number), in `xmm7` as GHASH's registers hold it; then the reduction
constant in `xmm1`, `H'` in `xmm3` and `Y = 0` in `xmm2`. -/
def hkey : List Instr :=
  ([.mov .rax (.mem (at_ .r15 akO)), .mov .rdx (.mem (at_ .r15 (akO + 8))), .mov .rcx (.reg .rax),
    .alu .and .rcx (imm 1), .mov32 .r8 (imm 0), .alu .sub .r8 (.reg .rcx), .shift .shr .rax 1,
    .mov .rcx (.reg .rdx), .alu .and .rcx (imm 1), .shift .ror .rcx 1, .alu .or .rax (.reg .rcx), .shift .shr .rdx 1,
    .movImm64 .rcx 0xE100000000000000, .alu .and .rcx (.reg .r8), .alu .xor .rdx (.reg .rcx),
    .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .rdx), .xop (.bin .punpcklqdq .xmm7 .xmm11)] : List Instr) ++
  constImm .xmm1 poly ++ hInvImm ++ ([.xop (.bin .pxor .xmm2 .xmm2)] : List Instr)

/-- The block at `r12 + 16 j` into `xmm7`, as it is. -/
def ld (j : Nat) : List Instr := [.movdquLoad .xmm7 (at_ .r12 (16 * j))]

/-- `Y ← (Y ⊕ xmm7) · H`. -/
def mulY : List Instr :=
  zero ++ ([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ acc .xmm7 .xmm3 ++ reduce .xmm2

/-- One block at `r12` absorbed; `r12` past it and `rbx` one fewer. -/
def body1 : List Instr :=
  ld 0 ++ mulY ++ ([.alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] : List Instr)

/-- Four blocks at `r12` absorbed; `r12` past them, `rbx` four fewer,
compared with 4. -/
def body4 : List Instr :=
  zero ++ ld 0 ++ ([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ acc .xmm7 .xmm6 ++
  ld 1 ++ acc .xmm7 .xmm5 ++ ld 2 ++ acc .xmm7 .xmm4 ++ ld 3 ++ acc .xmm7 .xmm3 ++
  reduce .xmm2 ++ ([.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4), .alu .cmp .rbx (imm 4)] : List Instr)

/-- The `rbx` whole blocks at `r12` absorbed, after `test rbx, rbx`: with
`four`, four at a time while there are four (with `H'²`–`H'⁴`, computed only
then), and the others one at a time. -/
def absorbBlocks (four : Bool) : Prog isa :=
  if four then
    .ite .e (.block [])
      (.seq (.block [.alu .cmp .rbx (imm 4)])
        (.seq (.ite .b (.block []) (.seq (.block pows) (.loop (.block body4) .ae)))
          (.seq (.block [.alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop (.block body1) .ne)))))
  else .ite .e (.block []) (.loop (.block body1) .ne)

/-- The last `rcx` (1 to 15) bytes at `rsi`, padded with zeros at `W + bO`,
absorbed. -/
def absorbTail : Prog isa :=
  .seq (.block (ptr .rdi .r15 bO ++ ([.xop (.bin .pxor .xmm7 .xmm7), .movdquStore (at_ .rdi 0) .xmm7] : List Instr)))
    (.seq copyLoop (.block (([.movdquLoad .xmm7 (at_ .rdi 0)] : List Instr) ++ mulY)))

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, absorbed. -/
def absorb (four : Bool) : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .test .rbx (.reg .rbx)])
    (.seq (absorbBlocks four)
      (.seq (.block [.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block []) absorbTail)))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, absorbed. -/
def lens : List Instr :=
  ([.mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax),
    .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
    .alu .add .rdx (.reg .rdx),
    .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .rdx), .xop (.bin .punpcklqdq .xmm7 .xmm11)] : List Instr) ++ mulY

/-- POLYVAL of the additional data, the data and the lengths, in `xmm2`. -/
def polyval : Prog isa :=
  .seq (.block (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)))
    (.seq (absorb false)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
        (.seq (absorb true) (.block lens))))

/-! ## The tag -/

/-- The tag input in `xmm0`: POLYVAL's result, its first 12 bytes XORed with
the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.movqR .rax .xmm2, .xop (.shift .psrldq .xmm2 8), .movqR .rdx .xmm2,
   .mov .rcx (.mem (at_ .r15 nonceO)), .alu .xor .rax (.mem (at_ .rcx 0)), .mov32 .r8 (.mem (at_ .rcx 8)),
   .alu .xor .rdx (.reg .r8), .movImm64 .r8 0x7FFFFFFFFFFFFFFF, .alu .and .rdx (.reg .r8),
   .xop (.movq .xmm0 .rax), .xop (.movq .xmm1 .rdx), .xop (.bin .punpcklqdq .xmm0 .xmm1)]

/-- The tag at `W + o`, from POLYVAL's result in `xmm2`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (tagIn ++ aesArgs (ptr .rdi .r15 skO)))
    (.seq (aes [.xmm0]) (.block [.movdquStore (at_ .r15 o) .xmm0]))

/-! ## Counter mode -/

/-- The counter block in `xmm9`, the tag at `W` with the top bit of its last
byte set; its increment in `xmm10`; `aes`'s arguments; and the data in
`r12`, its whole blocks counted in `rbx`. -/
def ctrInit : List Instr :=
  ([.movdquLoad .xmm0 (at_ .r15 tagO), .movImm64 .rax 0x8000000000000000, .xop (.movq .xmm9 .rax),
    .xop (.shift .pslldq .xmm9 8), .xop (.bin .por .xmm9 .xmm0), .mov32 .rax (imm 1),
    .xop (.movq .xmm10 .rax)] : List Instr) ++ aesArgs (ptr .rdi .r15 skO) ++
  ([.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
    .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)] : List Instr)

/-- The next counter blocks into `regs`. -/
def ctrs : List XReg → List Instr
  | [] => []
  | b :: bs => ([.xop (.bin .movdqa b .xmm9), .xop (.bin .paddd .xmm9 .xmm10)] : List Instr) ++ ctrs bs

/-- The keystream block in `b` XORed into the 16 bytes at `r12 + 16 j`. -/
def xorData (b : XReg) (j : Nat) : List Instr :=
  [.movdquLoad .xmm8 (at_ .r12 (16 * j)), .xop (.bin .pxor b .xmm8), .movdquStore (at_ .r12 (16 * j)) b]

/-- Four blocks at `r12` enciphered; `r12` past them, `rbx` four fewer,
compared with 4. -/
def crypt4 : Prog isa :=
  .seq (.block (ctrs [.xmm0, .xmm1, .xmm2, .xmm3]))
    (.seq (aes [.xmm0, .xmm1, .xmm2, .xmm3])
      (.block (xorData .xmm0 0 ++ xorData .xmm1 1 ++ xorData .xmm2 2 ++ xorData .xmm3 3 ++
        ([.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4), .alu .cmp .rbx (imm 4)] : List Instr))))

/-- One block at `r12` enciphered; `r12` past it and `rbx` one fewer. -/
def crypt1 : Prog isa :=
  .seq (.block (ctrs [.xmm0]))
    (.seq (aes [.xmm0])
      (.block (xorData .xmm0 0 ++ ([.alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] : List Instr))))

/-- The last `rbp` (1 to 15) bytes of the data, at `r12`, XORed with a
keystream block at `W + bO`. -/
def cryptTail : Prog isa :=
  .seq (.block (ctrs [.xmm0]))
    (.seq (aes [.xmm0])
      (.seq (.block (ptr .rsi .r15 bO ++ ([.movdquStore (at_ .rsi 0) .xmm0, .mov .rdi (.reg .r12),
          .mov .rcx (.reg .rbp)] : List Instr)))
        xorLoop))

/-- The `rbx` whole blocks at `r12` and the `rbp` (below 16) bytes after
them enciphered, after `test rbx, rbx`, from the counter block in `xmm9`. -/
def cryptRest : Prog isa :=
  .seq (.ite .e (.block [])
      (.seq (.block [.alu .cmp .rbx (imm 4)])
        (.seq (.ite .b (.block []) (.loop crypt4 .ae))
          (.seq (.block [.alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop crypt1 .ne))))))
    (.seq (.block [.alu .test .rbp (.reg .rbp)])
      (.ite .e (.block []) cryptTail))

/-- The data enciphered (or deciphered) in place, from the tag at `W`. -/
def crypt : Prog isa := .seq (.block ctrInit) cryptRest

/-! ## The functions -/

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq keys (.seq polyval (.seq (tag tagO) (.seq crypt (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq keys (.seq crypt (.seq polyval (.seq (tag bO)
    (.seq (.block cmp) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))

/-! ## With loops on the data's 256-byte groups

From 256 bytes of data, `sealL` and `openL` run the loops `L` of
`Impl/AesGcmSiv/X86_64Stitch.lean` on the data's groups of sixteen blocks,
and the code above on the rest. The loops take their arguments in memory:
`H` and `Y`, in GHASH's order, at `W + 64` and `W + 80`, the counter block
at `W + 96`, and 256 bytes for the powers of `H` at `W + 488`, after the
encryption key's schedule. -/

open VG.Impl.AesGcmSiv.X86_64 (hO yO cmO)
open VG.Impl.Gcm.X86_64.Pclmul (revMask)
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)

/-- The powers' working space, in `W`. -/
def pO : Nat := 488

/-- `Y`, from `xmm2`, and `H` stored for the loops, in GHASH's order. -/
def putYH : List Instr :=
  constImm .xmm0 revMask ++
  ([.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .r15 yO) .xmm2] : List Instr) ++ hkey ++
  constImm .xmm0 revMask ++
  ([.xop (.bin .pshufb .xmm7 .xmm0), .movdquStore (at_ .r15 hO) .xmm7] : List Instr)

/-- The data after its 256-byte groups: its address (`r12`) and length
(`rbp`). -/
def restLoad : List Instr :=
  [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rax (.reg .rbp),
    .shift .shr .rax 8, .shift .shl .rax 8, .alu .add .r12 (.reg .rax), .alu .and .rbp (imm 255)]

/-- POLYVAL's registers again after a loop, `Y` from where the loop left
it, and the rest of the data. -/
def back : List Instr :=
  hkey ++ constImm .xmm0 revMask ++
  ([.movdquLoad .xmm2 (at_ .r15 yO), .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++ restLoad

/-- The groups' blocks, counted in `r9`. -/
def groups : List Instr := [.mov .r9 (.mem (at_ .r15 lenO)), .shift .shr .r9 8, .shift .shl .r9 4]

/-- `hash`'s arguments, but `Y` and `H`. -/
def hashPtrs : List Instr :=
  ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 pO ++
  ([.mov .rdx (.mem (at_ .r15 dataO))] : List Instr) ++ groups

/-- `hash`'s arguments. -/
def hashArgs : List Instr := putYH ++ hashPtrs

/-- The data's length compared with 256. -/
def lenCmp : List Instr := [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 256)]

/-- The data's groups absorbed by `L.hash`. -/
def hashFront (L : Loops) : Prog isa := .seq (.block hashArgs) (.seq L.hash (.block back))

/-- POLYVAL, as `polyval`, the data's 256-byte groups with `L.hash`. -/
def polyvalL (L : Loops) : Prog isa :=
  .seq (.block (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)))
    (.seq (absorb false)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
        (.seq (.block lenCmp)
          (.seq (.ite .b (.block []) (hashFront L))
            (.seq (absorb true) (.block lens))))))

/-- The groups' count, the counter block, from `xmm9`, at `W + 96`, and the
loops' pointers. -/
def ctrPtrs : List Instr :=
  groups ++ (([.movdquStore (at_ .r15 cmO) .xmm9] : List Instr) ++ ptr .rdx .r15 cmO ++ ptr .rcx .r15 yO ++
    ptr .r8 .r15 hO ++ ptr .r11 .r15 pO)

/-- `ctr`'s and `dec`'s arguments, but `Y` and `H`: the counter block, from
the tag at `W`, at `W + 96`. -/
def ctrArgs : List Instr := ctrInit ++ ctrPtrs

/-- The counter block from `W + 96`, its increment, and `aes`'s arguments. -/
def ctrLoad : List Instr :=
  ([.movdquLoad .xmm9 (at_ .r15 cmO), .mov32 .rax (imm 1), .xop (.movq .xmm10 .rax)] : List Instr) ++
  aesArgs (ptr .rdi .r15 skO)

/-- The whole blocks of the `rbp` bytes counted in `rbx`, the last bytes in
`rbp`. -/
def split16 : List Instr :=
  [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]

/-- Counter mode's registers again after a loop, the counter block from
where the loop left it, and the rest of the data, as `ctrInit` leaves them. -/
def ctrBack : List Instr := ctrLoad ++ (restLoad ++ split16)

/-- The data's groups enciphered by `L.ctr`, then the rest. -/
def ctrFront (L : Loops) : Prog isa :=
  .seq (.block ctrArgs) (.seq L.ctr (.seq (.block ctrBack) cryptRest))

/-- Counter mode, as `crypt`, the data's 256-byte groups with `L.ctr`. -/
def cryptL (L : Loops) : Prog isa :=
  .seq (.block lenCmp)
    (.ite .b crypt (ctrFront L))

/-- `vg_aes_gcm_siv_seal`, with the loops `L` from 256 bytes of data. -/
def sealL (L : Loops) : Prog isa :=
  .seq (.block entry) (.seq keys (.seq (polyvalL L) (.seq (tag tagO) (.seq (cryptL L) (.block (tagOut ++ restore))))))

/-- The data's groups deciphered and absorbed by `L.dec`, then the rest
deciphered. -/
def decFront (L : Loops) : Prog isa :=
  .seq (.block (putYH ++ ctrArgs)) (.seq L.dec (.seq (.block ctrBack) cryptRest))

/-- With 256 bytes of data or more: POLYVAL of the additional data, the
data deciphered and its groups absorbed (`decFront`), then the rest of the
plaintext absorbed, and the lengths. -/
def decL (L : Loops) : Prog isa :=
  .seq (.block (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)))
    (.seq (absorb false)
      (.seq (decFront L) (.seq (.block back) (.seq (absorb true) (.block lens)))))

/-- `vg_aes_gcm_siv_open`, with the loops `L` from 256 bytes of data. -/
def openL (L : Loops) : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq keys (.seq (.block lenCmp)
    (.seq (.ite .b (.seq crypt polyval) (decL L)) (.seq (tag bO)
      (.seq (.block cmp) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))

end VG.Impl.AesGcmSiv.X86_64Reg
