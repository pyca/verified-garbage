module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# AES-GCM-SIV with AES-NI and PCLMULQDQ: the keys, POLYVAL and the counters in registers

`vg_aes_gcm_siv_seal(schedule = rdi, rounds = rsi, nonce = rdx, aad = rcx, aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16], work = [rsp + 24])`
and `vg_aes_gcm_siv_open` with the same arguments (`Spec/GcmSiv/Contract.lean`),
for CPUs with AES-NI, PCLMULQDQ and SSSE3, with no calls: what
`Impl/AesGcmSiv/X86_64.lean` passes between the functions it calls through
its working space (the message keys' blocks, POLYVAL's key and accumulator,
the reversed blocks, the counter blocks and the keystream) stays in
registers here, and the working space holds only the encryption key's
schedule, the two message keys and one block.

* The message keys (RFC 8452 §4): the blocks
  `little_endian_uint32(i) ‖ nonce` are encrypted two at a time
  (`Impl.Aes.X86_64.AesNi.aes`), and the first 8 bytes of each pair stored
  with one 16-byte store, from `W + 240` (`derive`).
* The encryption key's schedule at `W`: `AesNi.expandKey`, inline (`expand`).
* POLYVAL (§3) is GHASH on the same bits with the key `H · x` on blocks in
  the other byte order (`Proof.GcmSiv.Polyval`): GHASH's registers
  (`Impl.Gcm.X86_64.Pclmul`) hold each block as loaded, with no byte
  reversal, and `Y` as POLYVAL's result. The additional data is absorbed a
  block at a time, the data four blocks at a time with `H'`–`H'⁴` and then
  one at a time; a last partial block is copied to `W + 288`, padded with
  zeros (`absorb`); the lengths block is built in registers (`lens`).
* The tag is the encryption of the tag input, built in registers (`tagIn`).
* Counter mode (§4) increments the first 32-bit word of the counter block:
  `paddd` on the block as it is, four blocks at a time and then one at a
  time, XORed into the data in place; the last bytes are XORed with a
  keystream block at `W + 288` (`crypt`).
* `open` deciphers first, from the received tag, computes the tag of the
  plaintext, compares the two without a branch and ANDs the data with
  `0 − ok` (`cmpMask`).

## The working space `W` (320 bytes)

`[0, 240)`: the encryption key's schedule; `[240, 256)`: the authentication
key; `[256, 288)`: the encryption key; `[288, 304)`: a block; `[304, 312)`:
`rounds`; `[312, 320)`: `aad`, which `open` needs after counter mode.

## Registers

`rdx` the nonce, `r8` `aad_len` and `r9` the data throughout (`aad` is
reloaded from `W`) (`r11` holds the
nonce across `expandKey`, which takes `rdx`). `rdi`, `rsi` and `r10` are the
schedule, `rounds` and the last round key's address for `aes` (`aesArgs`),
`rcx` the bytes being absorbed or enciphered, `r11` a count, `rax` a
temporary. `xmm1`–`xmm11` are GHASH's (`Pclmul`); counter mode uses
`xmm0`–`xmm3` for the blocks, `xmm8` for the round key, `xmm9` for the
counter block and `xmm10` for its increment.

Only the pointers, the lengths and `rounds` (and for `open`, whether the tag
is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64Reg

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm copyLoop xorLoop)
open VG.Impl.Aes.X86_64.AesNi (aes expandKey)
open VG.Impl.Gcm.X86_64.Pclmul (zero acc reduce pows poly constImm hInvImm)

def akO : Nat := 240
def ekO : Nat := 256
def bO : Nat := 288
def roundsO : Nat := 304
def aadO : Nat := 312

/-- The size of the working space. -/
def workLen : Nat := 320

/-- `len`, `tag` and the working space, on the stack. -/
def lenArg : MemOp := at_ .rsp 8
def tagArg : MemOp := at_ .rsp 16
def workArg : MemOp := at_ .rsp 24

/-- The last round key's address for `aes`, from the schedule in `rdi` and
`rounds` in `rsi`. -/
def lastKey : List Instr := [.mov .r10 (.reg .rsi), .shift .shl .r10 4, .alu .add .r10 (.reg .rdi)]

/-- `aes`'s arguments for the encryption key: its schedule at `W`. -/
def aesArgs : List Instr :=
  ([.mov .rdi (.mem workArg), .mov .rsi (.mem (at_ .rdi roundsO))] : List Instr) ++ lastKey

/-- `rounds` and `aad` kept in `W`, and `aes`'s arguments for the key-generating
key. -/
def entry : List Instr :=
  ([.mov .rax (.mem workArg), .store (at_ .rax roundsO) .rsi, .store (at_ .rax aadO) .rcx] : List Instr) ++ lastKey

/-! ## The keys -/

/-- The blocks `little_endian_uint32(r11) ‖ nonce` and
`little_endian_uint32(r11 + 1) ‖ nonce` in `xmm0` and `xmm1` (`r11` even,
below 6). -/
def derivePair : List Instr :=
  [.mov .rax (.mem (at_ .rdx 4)), .xop (.movq .xmm2 .rax),
   .mov32 .rax (.mem (at_ .rdx 0)), .shift .shl .rax 32, .alu .or .rax (.reg .r11),
   .xop (.movq .xmm0 .rax), .xop (.bin .punpcklqdq .xmm0 .xmm2),
   .alu .add .rax (imm 1), .xop (.movq .xmm1 .rax), .xop (.bin .punpcklqdq .xmm1 .xmm2)]

/-- The first 8 bytes of `xmm0` and of `xmm1` at `W + akO + 8 · r11`, with
one 16-byte store; `r11` two more, compared with `rounds / 2 − 1`. -/
def deriveKeep : List Instr :=
  [.xop (.bin .punpcklqdq .xmm0 .xmm1),
   .mov .rax (.reg .r11), .shift .shl .rax 3, .alu .add .rax (.mem workArg),
   .movdquStore (at_ .rax akO) .xmm0,
   .alu .add .r11 (imm 2), .mov .rax (.reg .rsi), .shift .shr .rax 1, .alu .sub .rax (imm 1),
   .alu .cmp .r11 (.reg .rax)]

/-- The message keys, 8 bytes per block, from `W + akO`. -/
def derive : Prog isa :=
  .seq (.block [.mov32 .r11 (imm 0)])
    (.loop (.seq (.block derivePair) (.seq (aes [.xmm0, .xmm1]) (.block deriveKeep))) .ne)

/-- The encryption key's schedule at `W`: its length is `4 (rounds − 6)`. -/
def expand : Prog isa :=
  .seq (.block [.mov .r11 (.reg .rdx), .mov .rdx (.mem workArg), .mov .rdi (.reg .rdx),
      .alu .add .rdi (imm ekO), .mov .rsi (.mem (at_ .rdx roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)])
    (.seq expandKey (.block [.mov .rdx (.reg .r11)]))

/-! ## POLYVAL -/

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number), in `xmm7` as GHASH's registers hold it; then the reduction
constant in `xmm1`, `H'` in `xmm3`, `Y = 0` in `xmm2` and `aad` in `rcx`. -/
def hkey : List Instr :=
  ([.mov .rdi (.mem workArg), .mov .rax (.mem (at_ .rdi akO)), .mov .r10 (.mem (at_ .rdi (akO + 8))),
    .mov .rsi (.reg .rax), .alu .and .rsi (imm 1), .mov32 .r11 (imm 0), .alu .sub .r11 (.reg .rsi),
    .shift .shr .rax 1, .mov .rsi (.reg .r10), .alu .and .rsi (imm 1), .shift .ror .rsi 1,
    .alu .or .rax (.reg .rsi), .shift .shr .r10 1, .movImm64 .rsi 0xE100000000000000,
    .alu .and .rsi (.reg .r11), .alu .xor .r10 (.reg .rsi),
    .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .r10), .xop (.bin .punpcklqdq .xmm7 .xmm11)] : List Instr) ++
  constImm .xmm1 poly ++ hInvImm ++ ([.xop (.bin .pxor .xmm2 .xmm2), .mov .rcx (.mem (at_ .rdi aadO))] : List Instr)

/-- The block at `rcx + 16 j` into `xmm7`, as it is. -/
def ld (j : Nat) : List Instr := [.movdquLoad .xmm7 (at_ .rcx (16 * j))]

/-- `Y ← (Y ⊕ xmm7) · H`. -/
def mulY : List Instr :=
  zero ++ ([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ acc .xmm7 .xmm3 ++ reduce .xmm2

/-- One block at `rcx` absorbed; `rcx` past it and `r11` one fewer. -/
def body1 : List Instr :=
  ld 0 ++ mulY ++ ([.alu .add .rcx (imm 16), .alu .sub .r11 (imm 1)] : List Instr)

/-- Four blocks at `rcx` absorbed; `rcx` past them, `r11` four fewer,
compared with 4. -/
def body4 : List Instr :=
  zero ++ ld 0 ++ ([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++ acc .xmm7 .xmm6 ++
  ld 1 ++ acc .xmm7 .xmm5 ++ ld 2 ++ acc .xmm7 .xmm4 ++ ld 3 ++ acc .xmm7 .xmm3 ++
  reduce .xmm2 ++ ([.alu .add .rcx (imm 64), .alu .sub .r11 (imm 4), .alu .cmp .r11 (imm 4)] : List Instr)

/-- The `r11` whole blocks at `rcx` absorbed, after `test r11, r11`: with
`four`, four at a time while there are four (with `H'²`–`H'⁴`, computed only
then), and the others one at a time. -/
def absorbBlocks (four : Bool) : Prog isa :=
  if four then
    .ite .e (.block [])
      (.seq (.block [.alu .cmp .r11 (imm 4)])
        (.seq (.ite .b (.block []) (.seq (.block pows) (.loop (.block body4) .ae)))
          (.seq (.block [.alu .test .r11 (.reg .r11)]) (.ite .e (.block []) (.loop (.block body1) .ne)))))
  else .ite .e (.block []) (.loop (.block body1) .ne)

/-- The last `rcx` (1 to 15) bytes at `rsi`, padded with zeros at `W + bO`,
absorbed. -/
def absorbTail : Prog isa :=
  .seq (.block [.mov .rdi (.mem workArg), .alu .add .rdi (imm bO), .xop (.bin .pxor .xmm7 .xmm7),
      .movdquStore (at_ .rdi 0) .xmm7])
    (.seq copyLoop (.block (([.movdquLoad .xmm7 (at_ .rdi 0)] : List Instr) ++ mulY)))

/-- The `len` bytes at `rcx`, padded with zeros to whole blocks, absorbed. -/
def absorb (len : Src) (four : Bool) : Prog isa :=
  .seq (.block [.mov .r11 len, .shift .shr .r11 4, .alu .test .r11 (.reg .r11)])
    (.seq (absorbBlocks four)
      (.seq (.block [.mov .rsi (.reg .rcx), .mov .rcx len, .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block []) absorbTail)))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, absorbed. -/
def lens : List Instr :=
  ([.mov .rax (.reg .r8), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .mov .r11 (.mem lenArg), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11),
    .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .r11), .xop (.bin .punpcklqdq .xmm7 .xmm11)] : List Instr) ++ mulY

/-- POLYVAL of the additional data, the data and the lengths, in `xmm2`. -/
def polyval : Prog isa :=
  .seq (.block hkey)
    (.seq (absorb (.reg .r8) false)
      (.seq (.block [.mov .rcx (.reg .r9)])
        (.seq (absorb (.mem lenArg) true) (.block lens))))

/-! ## The tag -/

/-- The tag input in `xmm0`: POLYVAL's result, its first 12 bytes XORed with
the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.movqR .rax .xmm2, .xop (.shift .psrldq .xmm2 8), .movqR .r10 .xmm2,
   .alu .xor .rax (.mem (at_ .rdx 0)), .mov32 .r11 (.mem (at_ .rdx 8)), .alu .xor .r10 (.reg .r11),
   .movImm64 .r11 0x7FFFFFFFFFFFFFFF, .alu .and .r10 (.reg .r11),
   .xop (.movq .xmm0 .rax), .xop (.movq .xmm1 .r10), .xop (.bin .punpcklqdq .xmm0 .xmm1)]

/-- The tag in `xmm0`, from POLYVAL's result in `xmm2`. -/
def tag : Prog isa := .seq (.block (tagIn ++ aesArgs)) (aes [.xmm0])

/-! ## Counter mode -/

/-- The counter block in `xmm9`, the tag in `xmm0` with the top bit of its
last byte set; its increment in `xmm10`; `aes`'s arguments; and the data in
`rcx`, its whole blocks counted in `r11`. -/
def ctrInit : List Instr :=
  ([.movImm64 .rax 0x8000000000000000, .xop (.movq .xmm9 .rax), .xop (.shift .pslldq .xmm9 8),
    .xop (.bin .por .xmm9 .xmm0), .mov32 .rax (imm 1), .xop (.movq .xmm10 .rax)] : List Instr) ++ aesArgs ++
  ([.mov .rcx (.reg .r9), .mov .r11 (.mem lenArg), .shift .shr .r11 4, .alu .test .r11 (.reg .r11)] : List Instr)

/-- The next counter blocks into `regs`. -/
def ctrs : List XReg → List Instr
  | [] => []
  | b :: bs => ([.xop (.bin .movdqa b .xmm9), .xop (.bin .paddd .xmm9 .xmm10)] : List Instr) ++ ctrs bs

/-- The keystream block in `b` XORed into the 16 bytes at `rcx + 16 j`. -/
def xorData (b : XReg) (j : Nat) : List Instr :=
  [.movdquLoad .xmm8 (at_ .rcx (16 * j)), .xop (.bin .pxor b .xmm8), .movdquStore (at_ .rcx (16 * j)) b]

/-- Four blocks at `rcx` enciphered; `rcx` past them, `r11` four fewer,
compared with 4. -/
def crypt4 : Prog isa :=
  .seq (.block (ctrs [.xmm0, .xmm1, .xmm2, .xmm3]))
    (.seq (aes [.xmm0, .xmm1, .xmm2, .xmm3])
      (.block (xorData .xmm0 0 ++ xorData .xmm1 1 ++ xorData .xmm2 2 ++ xorData .xmm3 3 ++
        ([.alu .add .rcx (imm 64), .alu .sub .r11 (imm 4), .alu .cmp .r11 (imm 4)] : List Instr))))

/-- One block at `rcx` enciphered; `rcx` past it and `r11` one fewer. -/
def crypt1 : Prog isa :=
  .seq (.block (ctrs [.xmm0]))
    (.seq (aes [.xmm0])
      (.block (xorData .xmm0 0 ++ ([.alu .add .rcx (imm 16), .alu .sub .r11 (imm 1)] : List Instr))))

/-- The last bytes of the data, at `rcx` (their number, 1 to 15, in `r11`),
XORed with a keystream block at `W + bO`. -/
def cryptTail : Prog isa :=
  .seq (.block (ctrs [.xmm0]))
    (.seq (aes [.xmm0])
      (.seq (.block [.mov .rsi (.mem workArg), .alu .add .rsi (imm bO), .movdquStore (at_ .rsi 0) .xmm0,
          .mov .rdi (.reg .rcx), .mov .rcx (.reg .r11)])
        xorLoop))

/-- The data enciphered (or deciphered) in place, from the tag in `xmm0`. -/
def crypt : Prog isa :=
  .seq (.block ctrInit)
    (.seq (.ite .e (.block [])
        (.seq (.block [.alu .cmp .r11 (imm 4)])
          (.seq (.ite .b (.block []) (.loop crypt4 .ae))
            (.seq (.block [.alu .test .r11 (.reg .r11)]) (.ite .e (.block []) (.loop crypt1 .ne))))))
      (.seq (.block [.mov .r11 (.mem lenArg), .alu .and .r11 (imm 15), .alu .test .r11 (.reg .r11)])
        (.ite .e (.block []) cryptTail)))

/-! ## Comparing tags and masking -/

/-- `ok` (1 if the tag in `xmm0` is the one at `tag`, 0 if not, without a
branch) in `r8`, `0 − ok` in `r11` and in both halves of `xmm0`; the data in
`rcx`, its whole blocks counted in `rax`. -/
def cmp : List Instr :=
  [.mov .rax (.mem tagArg), .movdquLoad .xmm1 (at_ .rax 0), .xop (.bin .pxor .xmm0 .xmm1),
   .movqR .rax .xmm0, .xop (.shift .psrldq .xmm0 8), .movqR .r10 .xmm0, .alu .or .rax (.reg .r10),
   .alu .cmp .rax (imm 1), .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0), .mov .r8 (.reg .rax),
   .mov32 .r11 (imm 0), .alu .sub .r11 (.reg .rax),
   .xop (.movq .xmm0 .r11), .xop (.bin .punpcklqdq .xmm0 .xmm0),
   .mov .rcx (.reg .r9), .mov .rax (.mem lenArg), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]

/-- `[rcx + r10]`. -/
def maskByte : MemOp := { base := .rcx, index := some .r10 }

/-- Every byte of the data ANDed with `0 − ok`: its whole blocks, then the
rest. -/
def mask : Prog isa :=
  .seq (.ite .e (.block [])
      (.loop (.block [.movdquLoad .xmm1 (at_ .rcx 0), .xop (.bin .pand .xmm1 .xmm0), .movdquStore (at_ .rcx 0) .xmm1,
        .alu .add .rcx (imm 16), .alu .sub .rax (imm 1)]) .ne))
    (.seq (.block [.mov .rsi (.mem lenArg), .alu .and .rsi (imm 15), .mov32 .r10 (imm 0), .alu .test .rsi (.reg .rsi)])
      (.ite .e (.block [])
        (.loop (.block [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
          .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rsi)]) .ne)))

/-! ## The functions -/

/-- The keys: the message keys, and the encryption key's schedule. -/
def keys : Prog isa := .seq (.block entry) (.seq derive expand)

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq keys (.seq polyval (.seq tag
    (.seq (.block [.mov .rax (.mem tagArg), .movdquStore (at_ .rax 0) .xmm0]) crypt)))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq keys (.seq (.block [.mov .rax (.mem tagArg), .movdquLoad .xmm0 (at_ .rax 0)])
    (.seq crypt (.seq polyval (.seq tag (.seq (.block cmp) (.seq mask (.block [.mov .rax (.reg .r8)])))))))

end VG.Impl.AesGcmSiv.X86_64Reg
