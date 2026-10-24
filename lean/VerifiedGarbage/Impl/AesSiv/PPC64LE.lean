module

public import VerifiedGarbage.Impl.AesCcm.PPC64LE

/-!
# AES-SIV: PPC64LE implementation

`vg_aes_siv_init(key = r3, key_len = r4, ctx = r5, scratch = r6)`,
`vg_aes_siv_encrypt(ctx = r3, rounds = r4, ads = r5, ads_count = r6, data = r7, len = r8, siv = r9, work = r10)`
and `vg_aes_siv_decrypt` with the same arguments (see `VG.Spec.Siv.initContract`
and the others), with the working space as a last argument, which a frame
on the stack allocates (`Impl.StackScratch.PPC64LE.withStackScratch`),
composed of calls of the verified `vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32`, as on ARMv7 (`Impl/AesSiv/Arm.lean`). PPC64LE has one
implementation of each, so these are not generic over them. A call (`bl`)
stores nothing in memory, so no stack is used but the frames.

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239), its
CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`.

## The working spaces

`init`'s (`scratch`, 2560 bytes): `[0, 2176)` the working space of the
functions called, `[2176, 2216)` our caller's `r14`–`r17` and our return
address.

`encrypt`'s and `decrypt`'s (`work`, `W`, 2576 bytes): `[0, 16)` the
synthetic IV (`encrypt` copies it to `siv` at the end, `decrypt` copies the
received one from `siv` at the start), `[16, 32)` a zero block, `[32, 64)`
the last bytes of S2V's last string (`tail`), `[64, 80)` the counter
`Q + i`, `[80, 96)` a keystream block,
`[96, 112)` the counter block passed to `vg_aes_ctr32`, `[112, 128)` the IV
`decrypt` computes, `[128, 232)` our caller's `r14`–`r25` and our return
address, `[240, 256)` a CMAC state, `[256, 272)` `dbl(D)`, `[272, 288)` S2V's
state `D`, and `[384, 2560)` the working space of the functions called.

## Registers

`r14` holds `W`, `r15` the key context, `r16` the rounds, `r22` the data,
`r23` its length and `r24` `siv` throughout; `r17` the next descriptor and
`r18` how many are left while S2V absorbs the associated data; `r19` the
string S2V absorbs (a component of associated data, or the data), `r20` its
length, and in `ctr` the data and the length left; `r21` the bytes of whole blocks a CMAC chains; `r25` how many blocks
of the tail it chains, then `decrypt`'s result. The functions called
preserve them (they are nonvolatile).

## The pieces

* `init` expands `K1` into the context, derives its subkeys after it and
  expands `K2` after them.
* `encrypt` and `decrypt` start S2V with `D = AES-CMAC(K1, <zero>)`
  (`vg_cmac_aes_finalize` of the zero block from a zero state), then, for
  each component `S` of associated data, compute `AES-CMAC(K1, S)` into the
  CMAC state with `vg_cmac_aes_update` over the whole blocks of `S` but its
  last 1 to 16 bytes and `vg_cmac_aes_finalize` of those (`cmacOf`), and
  replace `D` with `dbl(D)` XOR it.
* `encrypt` then finishes S2V with the plaintext into the IV (`finish`),
  encrypts the plaintext with CTR from the IV with two bits cleared, `Q`
  (`ctr`), as on AArch64: one call of `vg_aes_ctr32` from `Q` encrypts the
  first `k = ⌊len / 16⌋ mod 2³¹` whole blocks. As `vg_aes_ctr32` increments
  only the last 32 bits of its counter block, this needs them not to wrap
  around: `Q`'s are below `2³¹`, its bit 31 being one of the two cleared,
  and `k < 2³¹`. Then each block left (the last `len mod 16` bytes, and more
  only for data of `2³⁵` bytes or more): `vg_aes_ctr32` on a zero block with
  the counter block `Q + i` gives the keystream, whose first
  `min(16, left)` bytes are XORed into the data. The counter's second
  doubleword, as a big-endian integer, is below `2⁶³` in `Q` and grows by
  fewer than `2⁶⁰`, so `Q + i` changes only it, without a branch on it. Last,
  it copies the IV to `siv` (`sivOut`).
* `decrypt` then copies the IV it is given from `siv` to `W` (`sivIn`),
  decrypts with CTR from it, finishes S2V with the plaintext into
  `[112, 128)`, compares the two IVs without a branch and ANDs every byte of
  the data with the mask of the result.

`finish`, for a string `P` of `L` bytes: if `L < 16`, the tail is
`pad(P) XOR dbl(D)` and its CMAC is that of one complete block; otherwise,
with `nb = ⌊(L − 1) / 16⌋` whole blocks before the last 1 to 16 bytes,
`k = max(nb, 1) − 1` and `j = min(nb, 1)`, the tail is the last
`L − 16 k` bytes of `P` with `D` XORed into its last 16 (`P xorend D`), and
the CMAC chains the `k` blocks of `P`, then the first `j` blocks of the
tail, and finalizes the rest of the tail.

The model has no flags: the branches are on whether a register is zero.
Only the pointers, `rounds`, the key length, `ads_count`, `len` and the
lengths of the components can affect timing: the branches are on them, and
so are the numbers of calls, bytes copied and blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesSiv.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.Gather.PPC64LE (copyBytes)
open VG.Impl.CmacAes.Stream.PPC64LE (ekCall skCall updCall finCall)
open VG.Impl.AesCtr.PPC64LE (ctrCall)
open VG.Impl.AesCcm.PPC64LE (zero16 xorBytes maskBody)

/-! ## The working space -/

def zO : Nat := 16
def tailO : Nat := 32
def cntO : Nat := 64
def ksO : Nat := 80
def cbO : Nat := 96
def tO : Nat := 112
def lrO : Nat := 224
def stO : Nat := 240
def dbO : Nat := 256
def dO : Nat := 272
def scrO : Nat := 384

/-- Our caller's registers, and where we save them (`r14`, the base of the
restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r15, 136), (.r16, 144), (.r17, 152), (.r18, 160), (.r19, 168), (.r20, 176), (.r21, 184),
    (.r22, 192), (.r23, 200), (.r24, 208), (.r25, 216), (.r14, 128)]

/-- The 16 bytes at `W + a` XORed with those at `W + b`, into `W + d`. -/
def xor16 (a b d : Nat) : List Instr :=
  [.load .d .r9 .r14 a, .load .d .r10 .r14 b, .logic .xor .r9 .r9 .r10, .store .d .r9 .r14 d,
    .load .d .r9 .r14 (a + 8), .load .d .r10 .r14 (b + 8), .logic .xor .r9 .r9 .r10, .store .d .r9 .r14 (d + 8)]

/-- The arguments every call of a CMAC function shares: the key context, the
rounds, the state at `W + st` and the working space. -/
def macArgs (st : Nat) : List Instr := [mov .r3 .r15, mov .r4 .r16, .addi .r5 .r14 st, .addi .r8 .r14 scrO]

/-! ## `vg_aes_siv_init` -/

/-- Our caller's registers and the return address (in `r0`), and where `init`
saves them (`r17`, the base of the restore, last). -/
def initSaved : List (Reg × Nat) := [(.r0, 2208), (.r14, 2176), (.r15, 2184), (.r16, 2192), (.r17, 2200)]

/-- Saves the registers and keeps the key in `r14`, the half length
(`key_len / 2`) in `r15`, the context in `r16` and the scratch buffer in
`r17`; the arguments of
`vg_aes_expand_key_scratch(key = r3, key_len = r4, schedule = r5, scratch = r6)` for
`K1` are then those but the length. -/
def initPre : List Instr :=
  .mflr .r0 :: initSaved.map (fun (r, d) => .store .d r .r6 d) ++
    [mov .r14 .r3, .lsr .d .r15 .r4 1, mov .r16 .r5, mov .r17 .r6, mov .r4 .r15]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = r3, rounds = r4, subkeys = r5, scratch = r6)`,
the rounds `key_len / 8 + 6`. -/
def initMid₁ : List Instr := [mov .r3 .r16, .lsr .d .r4 .r15 2, .addi .r4 .r4 6, .addi .r5 .r16 240, mov .r6 .r17]

/-- The arguments of `vg_aes_expand_key_scratch` for `K2`. -/
def initMid₂ : List Instr := [.add .r3 .r14 .r15, mov .r4 .r15, .addi .r5 .r16 272, mov .r6 .r17]

/-- The return address and the registers restored. -/
def initPost : List Instr := initSaved.map (fun (r, d) => .load .d r .r17 d) ++ [.mtlr .r0]

def init : Prog isa :=
  .seq (.block initPre)
    (.seq ekCall (.seq (.block initMid₁) (.seq skCall (.seq (.block initMid₂) (.seq ekCall (.block initPost))))))

/-! ## S2V's first state -/

/-- Saves our caller's registers and the return address in `work` (`r10`),
and keeps the arguments in `r14`–`r18` and `r22`–`r24`. -/
def entry : List Instr :=
  .mflr .r0 :: saved.map (fun (r, d) => .store .d r .r10 d) ++
    [.store .d .r0 .r10 lrO, mov .r14 .r10, mov .r15 .r3, mov .r16 .r4, mov .r17 .r5, mov .r18 .r6,
      mov .r22 .r7, mov .r23 .r8, mov .r24 .r9]

/-- The zero block at `W + 16`, `D` zeroed, and the arguments of
`vg_cmac_aes_finalize(key = r3, rounds = r4, state = r5, last = r6, last_len = r7, scratch = r8)`
for the zero block. -/
def startPre : List Instr := zero16 zO ++ zero16 dO ++ macArgs dO ++ [.addi .r6 .r14 zO, .li .r7 16]

/-! ## The CMAC of a string -/

/-- With the string at `r19` (`r20` bytes): the CMAC state at `W + st`
zeroed, and `16 nb` in `r21` for the `nb` whole blocks before the last 1 to
16 bytes (none for the empty string). -/
def cmacLen (st : Nat) : Prog isa :=
  .seq (.block (zero16 st ++ [.li .r21 0]))
    (.ite (.zero .d .r20) (.block []) (.block [.subi .r21 .r20 1, .lsr .d .r21 .r21 4, .lsl .r21 .r21 4]))

/-- The arguments of `vg_cmac_aes_update(schedule = r3, rounds = r4, state = r5, data = r6, n = r7, scratch = r8)`
for the `nb` whole blocks. -/
def cmacArgs₁ (st : Nat) : List Instr := macArgs st ++ [mov .r6 .r19, .lsr .d .r7 .r21 4]

/-- The arguments of `vg_cmac_aes_finalize` for the last bytes. -/
def cmacArgs₂ (st : Nat) : List Instr := macArgs st ++ [.add .r6 .r19 .r21, .sub .r7 .r20 .r21]

/-- `AES-CMAC(K1, S)` into the 16 bytes at `W + st`. -/
def cmacOf (st : Nat) : Prog isa :=
  .seq (cmacLen st) (.seq (.block (cmacArgs₁ st)) (.seq updCall (.seq (.block (cmacArgs₂ st)) finCall)))

/-! ## Finishing S2V -/

/-- The short case, `L < 16`: the tail is `pad(P)`, the `L` bytes copied
onto zeros and `0x80` after them; then `dbl(D)`, at `W + 256`, is XORed into
it. -/
def shortTail : Prog isa :=
  .seq (.block (zero16 tailO))
    (.seq (.ite (.zero .d .r20) (.block []) (.seq (.block [mov .r3 .r19, .addi .r9 .r14 tailO, mov .r4 .r20]) copyBytes))
      (.block (([.add .r9 .r14 .r20, .li .r0 0x80, .stb .r0 .r9 tailO] : List Instr) ++
        Impl.CmacAes.PPC64LE.dbl dO dbO ++ xor16 tailO dbO tailO)))

/-- `16 k` in `r21`: `((L − 1) >> 4) − 1` shifted left by 4, or 0 if that is
negative. -/
def kBlock : Prog isa :=
  .seq (.block [.subi .r9 .r20 1, .lsr .d .r9 .r9 4, .li .r21 0])
    (.ite (.zero .d .r9) (.block []) (.block [.subi .r9 .r9 1, .lsl .r21 .r9 4]))

/-- `D` XORed into the 16 bytes at `r11 + 16`. -/
def xorD : List Instr :=
  [.load .d .r9 .r11 16, .load .d .r10 .r14 dO, .logic .xor .r9 .r9 .r10, .store .d .r9 .r11 16,
    .load .d .r9 .r11 24, .load .d .r10 .r14 (dO + 8), .logic .xor .r9 .r9 .r10, .store .d .r9 .r11 24]

/-- The last `L − 16 k` bytes (at least 16) of the string copied to the
tail, and `D` XORed into its last 16 bytes, at `W + 16 + (L − 16 k)`. -/
def tailCopy : Prog isa :=
  .seq (.block [.add .r3 .r19 .r21, .addi .r9 .r14 tailO, .sub .r4 .r20 .r21])
    (.seq copyBytes (.block ([.sub .r11 .r20 .r21, .add .r11 .r14 .r11] ++ xorD)))

/-- The long case, `L ≥ 16`: `16 k` in `r21`, and the tail. -/
def longTail : Prog isa := .seq kBlock tailCopy

/-- `j` in `r25`: 1 if `L > 16`, else 0. -/
def jBlock : Prog isa :=
  .seq (.block [.subi .r9 .r20 1, .lsr .d .r9 .r9 4, .li .r25 0])
    (.ite (.zero .d .r9) (.block []) (.block [.li .r25 1]))

/-- The state at `W + out` zeroed, and the arguments of `vg_cmac_aes_update`
over the `k` blocks of the string. -/
def longArgs₁ (out : Nat) : List Instr := zero16 out ++ macArgs out ++ [mov .r6 .r19, .lsr .d .r7 .r21 4]

/-- The arguments of `vg_cmac_aes_update` over the first `j` blocks of the
tail. -/
def longArgs₂ (out : Nat) : List Instr := macArgs out ++ [.addi .r6 .r14 tailO, mov .r7 .r25]

/-- The arguments of `vg_cmac_aes_finalize` over the rest of the tail. -/
def longArgs₃ (out : Nat) : List Instr :=
  macArgs out ++ [.addi .r6 .r14 tailO, .lsl .r9 .r25 4, .add .r6 .r6 .r9, .sub .r7 .r20 .r21, .sub .r7 .r7 .r9]

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail, then `vg_cmac_aes_finalize` of
the rest of the tail, into `W + out`. -/
def longMac (out : Nat) : Prog isa :=
  .seq (.block (longArgs₁ out))
    (.seq updCall
      (.seq jBlock (.seq (.block (longArgs₂ out)) (.seq updCall (.seq (.block (longArgs₃ out)) finCall)))))

/-- The state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
def shortArgs (out : Nat) : List Instr := zero16 out ++ macArgs out ++ [.addi .r6 .r14 tailO, .li .r7 16]

/-- The short case's call: `vg_cmac_aes_finalize` of the tail from a zero
state at `W + out`. -/
def shortMac (out : Nat) : Prog isa := .seq (.block (shortArgs out)) finCall

/-- S2V finished with the string at `r19` (`r20` bytes) from `D` at
`W + 272`, into the 16 bytes at `W + out`. -/
def finish (out : Nat) : Prog isa :=
  .seq (.block [.lsr .d .r9 .r20 4])
    (.ite (.zero .d .r9) (.seq shortTail (shortMac out)) (.seq longTail (longMac out)))

/-! ## CTR -/

/-- The 16 bytes at `W + a` copied to `W + b`. -/
def copy16 (a b : Nat) : List Instr :=
  [.load .d .r9 .r14 a, .store .d .r9 .r14 b, .load .d .r9 .r14 (a + 8), .store .d .r9 .r14 (b + 8)]

/-- The counter `Q` at `W + 64`: the IV at `W + src` with bit 7 of its bytes
8 and 12 cleared, by setting and flipping it (in its second doubleword,
read little-endian, bits 7 and 39). -/
def counter (src : Nat) : List Instr :=
  [.load .d .r9 .r14 src, .store .d .r9 .r14 cntO, .load .d .r9 .r14 (src + 8), .li .r10 0x80,
    .lsl .r11 .r10 32, .logic .or .r10 .r10 .r11, .logic .or .r9 .r9 .r10, .logic .xor .r9 .r9 .r10,
    .store .d .r9 .r14 (cntO + 8)]

/-- The arguments of `vg_aes_ctr32(schedule = r3, rounds = r4, counter = r5, data = r6, n = r7, scratch = r8)`
but the data and the number of blocks: `K2`'s schedule, the rounds, the
counter block at `W + 96` and the working space. -/
def ctrArgs : List Instr := [.addi .r3 .r15 272, mov .r4 .r16, .addi .r5 .r14 cbO, .addi .r8 .r14 scrO]

/-- `k = ⌊left / 16⌋ mod 2³¹` in `d`: the whole blocks `ctrWhole` does. -/
def wholeCount (d : Reg) : List Instr := [.lsr .d d .r20 4, .lsl d d 33, .lsr .d d d 33]

/-- The data and its length in `r19` and `r20`, the counter block `Q`, and
the arguments of `vg_aes_ctr32` over the first `k` whole blocks. -/
def wholePre : List Instr := [mov .r19 .r22, mov .r20 .r23] ++ copy16 cntO cbO ++ wholeCount .r7 ++ ctrArgs ++ [mov .r6 .r19]

/-- The counter `Q + k`, and the data advanced past the `16 k` bytes done.
Only the counter's second doubleword, as a big-endian integer, changes: it
is below `2⁶³` (bit 7 of byte 8 cleared), and the data has fewer than `2⁶⁰`
blocks, so it never carries into the first. -/
def wholePost : List Instr :=
  wholeCount .r9 ++ [.li .r11 (cntO + 8), .loadRev .d .r10 .r14 .r11, .add .r10 .r10 .r9, .storeRev .d .r10 .r14 .r11,
    .lsl .r9 .r9 4, .add .r19 .r19 .r9, .sub .r20 .r20 .r9]

/-- The first `k` whole blocks of the data, by one call of `vg_aes_ctr32`
from `Q` (none if `k` is 0). `Q`'s last 32 bits are below `2³¹` and
`k < 2³¹`, so its counter blocks do not wrap around. -/
def ctrWhole : Prog isa := .seq (.block wholePre) (.seq ctrCall (.block wholePost))

/-- The keystream block zeroed, the counter block `Q + i` passed to
`vg_aes_ctr32`, and its arguments for the keystream block. -/
def ctrPre : List Instr := zero16 ksO ++ copy16 cntO cbO ++ ctrArgs ++ [.addi .r6 .r14 ksO, .li .r7 1]

/-- `min(16, left)` in `r4`, and the keystream block and the data in `r3`
and `r9`. -/
def ctrMin : Prog isa :=
  .seq (.block [.lsr .d .r10 .r20 4, mov .r4 .r20, .addi .r3 .r14 ksO, mov .r9 .r19])
    (.ite (.zero .d .r10) (.block []) (.block [.li .r4 16]))

/-- The counter incremented (its second doubleword, which never carries);
the data advanced past the block. -/
def ctrPost : List Instr :=
  [.li .r11 (cntO + 8), .loadRev .d .r10 .r14 .r11, .addi .r10 .r10 1, .storeRev .d .r10 .r14 .r11,
    .addi .r19 .r19 16, .lsr .d .r9 .r20 4]

/-- The length left reduced by the block's (`min(16, left)`). -/
def ctrLeft : Prog isa := .ite (.zero .d .r9) (.block [.li .r20 0]) (.block [.subi .r20 .r20 16])

/-- One block of CTR: the first `min(16, left)` bytes of its keystream
XORed into the data. -/
def ctrBody : Prog isa :=
  .seq (.block ctrPre) (.seq ctrCall (.seq ctrMin (.seq xorBytes (.seq (.block ctrPost) ctrLeft))))

/-- The data (`len` bytes at `data`) XORed with the keystream of CTR under
`K2` from the counter `Q` the IV at `W + src` gives: its first `k` whole
blocks by `ctrWhole`, then the rest (the last `len mod 16` bytes, and more
only for data of `2³⁵` bytes or more) a block at a time. -/
def ctr (src : Nat) : Prog isa :=
  .seq (.block (counter src)) (.seq ctrWhole (.ite (.zero .d .r20) (.block []) (.loop ctrBody (.nonzero .d .r20))))

/-! ## Comparing the IVs and masking the data -/

/-- `r25 = 1` if the IVs at `W` and `W + 112` are equal, else 0, without a
branch: `d` the OR of the XORs of their doublewords, `1 − ((d | (0 − d)) >> 63)`. -/
def compare : List Instr :=
  [.load .d .r3 .r14 0, .load .d .r4 .r14 tO, .logic .xor .r3 .r3 .r4, .load .d .r4 .r14 8,
    .load .d .r5 .r14 (tO + 8), .logic .xor .r4 .r4 .r5, .logic .or .r3 .r3 .r4, .li .r4 0, .sub .r4 .r4 .r3,
    .logic .or .r3 .r3 .r4, .lsr .d .r3 .r3 63, .li .r25 1, .sub .r25 .r25 .r3]

/-- Every byte of the data ANDed with `0 − r25`: all ones if the IVs are
equal (`r25` is 1), zeros if not. -/
def mask : Prog isa :=
  .seq (.block [.li .r9 0, .sub .r9 .r9 .r25, mov .r3 .r22, mov .r4 .r23])
    (.ite (.zero .d .r4) (.block []) (.loop (.block maskBody) (.nonzero .d .r4)))

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

/-- The next component: its address in `r19` and its length in `r20`, from
the descriptor `r17` points to. -/
def adNext : List Instr := [.load .d .r19 .r17 0, .load .d .r20 .r17 8]

/-- `D = dbl(D) XOR` the CMAC state; then the next descriptor, and one
fewer left. -/
def adStep : List Instr :=
  Impl.CmacAes.PPC64LE.dbl dO dO ++ xor16 dO stO dO ++ [.addi .r17 .r17 16, .subi .r18 .r18 1]

/-- S2V of the components of associated data, from `D`'s first state. -/
def s2vAds : Prog isa :=
  .ite (.zero .d .r18) (.block [])
    (.loop (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) (.nonzero .d .r18))

/-- The data and its length in `r19` and `r20`. -/
def dataStr : List Instr := [mov .r19 .r22, mov .r20 .r23]

/-- The registers' saving, S2V's first state and S2V of the associated data,
then the data as S2V's string. -/
def encS2v : Prog isa :=
  .seq (.block (entry ++ startPre)) (.seq finCall (.seq s2vAds (.block dataStr)))

/-- The synthetic IV at `W` copied to `siv`. -/
def sivOut : List Instr := [.load .d .r9 .r14 0, .store .d .r9 .r24 0, .load .d .r9 .r14 8, .store .d .r9 .r24 8]

/-- The received synthetic IV at `siv` copied to `W`. -/
def sivIn : List Instr := [.load .d .r9 .r24 0, .store .d .r9 .r14 0, .load .d .r9 .r24 8, .store .d .r9 .r14 8]

/-- Restores the return address and our caller's registers (`r14`, the base,
last). -/
def restore : List Instr := [.load .d .r0 .r14 lrO, .mtlr .r0] ++ saved.map (fun (r, d) => .load .d r .r14 d)

def encrypt : Prog isa :=
  .seq encS2v (.seq (finish 0) (.seq (ctr 0) (.block (sivOut ++ restore))))

def decrypt : Prog isa :=
  .seq encS2v
    (.seq (.block sivIn) (.seq (ctr 0) (.seq (.block dataStr) (.seq (finish tO)
      (.seq (.block compare) (.seq mask (.block ([mov .r3 .r25] ++ restore))))))))

end VG.Impl.AesSiv.PPC64LE
