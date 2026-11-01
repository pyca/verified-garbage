module

public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# AES-SIV: RISC-V implementation

`vg_aes_siv_init(key = a0, key_len = a1, ctx = a2, scratch = a3)`,
`vg_aes_siv_encrypt(ctx = a0, rounds = a1, ads = a2, ads_count = a3, data = a4, len = a5, siv = a6, work = a7)`
and `vg_aes_siv_decrypt` with the same arguments (see `VG.Spec.Siv.initContract`
and the others), with the working space as a last argument, which a frame
on the stack allocates (`Impl.StackScratch.RISCV64.withStackScratch`),
composed of calls of the verified `vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32`, as on PPC64LE (`Impl/AesSiv/PPC64LE.lean`). RISC-V has one
implementation of each, so these are not generic over them. A call (`jal`)
stores nothing in memory, so no stack is used but the frames.

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239), its
CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`.

## The working spaces

`init`'s (`scratch`, 2560 bytes): `[0, 2176)` the working space of the
functions called, and from `scratch + 2176` rounded up to a multiple of 8
(`savePtr2`), our return address and our caller's `s1`–`s4`.

`encrypt`'s and `decrypt`'s (`work`, `W`, 2576 bytes, 8-byte aligned):
`[0, 16)` the synthetic IV (`encrypt` copies it to `siv` at the end,
`decrypt` copies the received one from `siv` at the start), `[16, 32)` a
zero block, `[32, 64)` the last bytes of S2V's last string (`tail`),
`[64, 80)` the counter `Q + i`, `[80, 96)` a keystream block, `[96, 112)` the
counter block passed to `vg_aes_ctr32`, `[112, 128)` the IV `decrypt`
computes, `[128, 232)` our caller's `s0`–`s11` and our return address,
`[240, 256)` a CMAC state, `[256, 272)` S2V's state `D`, `[272, 288)`
`dbl(D)`, and `[384, 2560)` the working space of the functions called.

## Registers

`s1` holds `W`, `s2` the key context, `s3` the rounds, `s9` the data, `s10`
its length and `s11` `siv` throughout; `s4` the next descriptor and `s5`
how many are left while S2V absorbs the associated data; `s6` the string
S2V absorbs (a component of associated data, or the data), `s7` its length,
and in `ctr` the data and the length left; `s8` the bytes of whole blocks a
CMAC chains; `s0` how many blocks of the tail it chains, then `decrypt`'s
result. The functions called preserve them (they are callee-saved).

## The pieces

As on PPC64LE; where it reads or writes a buffer whose alignment the
contracts do not state (the descriptors of the associated data, `siv`, and
the last 16 bytes of the tail, at any offset in `W`), RISC-V does so a byte
at a time:

* `init` expands `K1` into the context, derives its subkeys after it and
  expands `K2` after them.
* `encrypt` and `decrypt` start S2V with `D = AES-CMAC(K1, <zero>)`, then,
  for each component `S` of associated data (whose descriptor, its address
  and length, is read little-endian a byte at a time, `loadLE64`), compute
  `AES-CMAC(K1, S)` into the CMAC state with `vg_cmac_aes_update` over the
  whole blocks of `S` but its last 1 to 16 bytes and `vg_cmac_aes_finalize`
  of those (`cmacOf`), and replace `D` with `dbl(D)` XOR it (`dbl` a byte at
  a time, `Impl.Cmac.RISCV64.dbl`).
* `encrypt` then finishes S2V with the plaintext into the IV (`finish`),
  encrypts the plaintext with CTR from the IV with two bits cleared, `Q`
  (`ctr`): one call of `vg_aes_ctr32` from `Q` encrypts the first
  `k = ⌊len / 16⌋ mod 2³¹` whole blocks (`Q`'s last 32 bits are below `2³¹`,
  its bit 31 being one of the two cleared, and `k < 2³¹`, so they do not
  wrap around); then each block left with a keystream block from the
  counter block `Q + i`, whose second doubleword, read and written
  big-endian a byte at a time (`loadBE64`, `storeBE`), is below `2⁶³` in `Q`
  and grows by fewer than `2⁶⁰`, so `Q + i` changes only it. Last, it copies
  the IV to `siv` (`sivOut`).
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

The branches are on whether a register is zero, and the comparison of the
IVs is `sltu`'s. Only the pointers, `rounds`, the key length, `ads_count`,
`len` and the lengths of the components can affect timing: the branches
are on them, and so are the numbers of calls, bytes copied and blocks
chained.
-/

@[expose] public section

namespace VG.Impl.AesSiv.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Impl.CmacAes.Stream.RISCV64 (ekCall skCall updCall finCall savePtr2)
open VG.Impl.AesCtr.RISCV64 (ctrCall)
open VG.Impl.AesCcm.RISCV64 (zero16 copy xorBytes maskBody)
open VG.Impl.Cmac.RISCV64 (dbl)

/-! ## The working space -/

def zO : Nat := 16
def tailO : Nat := 32
def cntO : Nat := 64
def ksO : Nat := 80
def cbO : Nat := 96
def tO : Nat := 112
def raO : Nat := 224
def stO : Nat := 240
def dO : Nat := 256
def dbO : Nat := 272
def scrO : Nat := 384

/-- Our caller's registers, and where we save them (`s1`, the base of the
restore, last). -/
def saved : List (Reg × Nat) :=
  [(.s2, 136), (.s3, 144), (.s4, 152), (.s5, 160), (.s6, 168), (.s7, 176), (.s8, 184),
    (.s9, 192), (.s10, 200), (.s11, 208), (.s0, 216), (.s1, 128)]

/-- The 16 bytes at `W + a` XORed with those at `W + b`, into `W + d`. -/
def xor16 (a b d : Nat) : List Instr :=
  [.load .d .t0 .s1 a, .load .d .t1 .s1 b, .logic .xor .t0 .t0 .t1, .store .d .t0 .s1 d,
    .load .d .t0 .s1 (a + 8), .load .d .t1 .s1 (b + 8), .logic .xor .t0 .t0 .t1, .store .d .t0 .s1 (d + 8)]

/-- The arguments every call of a CMAC function shares: the key context, the
rounds, the state at `W + st` and the working space. -/
def macArgs (st : Nat) : List Instr :=
  [mov .a0 .s2, mov .a1 .s3, .addi .a2 .s1 (st : Int), .addi .a5 .s1 (scrO : Int)]

/-! ## `vg_aes_siv_init` -/

/-- Our caller's registers and the return address, and their offsets from
`t0` (`savePtr2`). -/
def initSaved : List (Reg × Nat) := [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32)]

/-- Saves them (with the scratch buffer in `a3`) and keeps the key in `s1`,
the half length (`key_len / 2`) in `s2`, the context in `s3` and the scratch
buffer in `s4`; the arguments of
`vg_aes_expand_key_scratch(key = a0, key_len = a1, schedule = a2, scratch = a3)`
for `K1` are then those but the length. -/
def initPre : List Instr :=
  savePtr2 .a3 ++ initSaved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .a0, .shift .srl .d .s2 .a1 1, mov .s3 .a2, mov .s4 .a3, mov .a1 .s2]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = a0, rounds = a1, subkeys = a2, scratch = a3)`,
the rounds `key_len / 8 + 6`. -/
def initMid₁ : List Instr :=
  [mov .a0 .s3, .shift .srl .d .a1 .s2 2, .addi .a1 .a1 6, .addi .a2 .s3 240, mov .a3 .s4]

/-- The arguments of `vg_aes_expand_key_scratch` for `K2`. -/
def initMid₂ : List Instr := [.add .a0 .s1 .s2, mov .a1 .s2, .addi .a2 .s3 272, mov .a3 .s4]

/-- The return address and the registers restored (with the scratch buffer in
`s4`). -/
def initPost : List Instr := savePtr2 .s4 ++ initSaved.map (fun (r, d) => .load .d r .t0 d)

def init : Prog isa :=
  .seq (.block initPre)
    (.seq ekCall (.seq (.block initMid₁) (.seq skCall (.seq (.block initMid₂) (.seq ekCall (.block initPost))))))

/-! ## S2V's first state -/

/-- Saves our caller's registers and the return address in `work` (`a7`),
and keeps the arguments in `s1`–`s5` and `s9`–`s11`. -/
def entry : List Instr :=
  saved.map (fun (r, d) => .store .d r .a7 d) ++
    [.store .d .ra .a7 raO, mov .s1 .a7, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s5 .a3,
      mov .s9 .a4, mov .s10 .a5, mov .s11 .a6]

/-- The zero block at `W + 16`, `D` zeroed, and the arguments of
`vg_cmac_aes_finalize(key = a0, rounds = a1, state = a2, last = a3, last_len = a4, scratch = a5)`
for the zero block. -/
def startPre : List Instr :=
  zero16 zO ++ zero16 dO ++ macArgs dO ++ [.addi .a3 .s1 (zO : Int), .li .a4 16]

/-! ## The CMAC of a string -/

/-- With the string at `s6` (`s7` bytes): the CMAC state at `W + st`
zeroed, and `16 nb` in `s8` for the `nb` whole blocks before the last 1 to
16 bytes (none for the empty string). -/
def cmacLen (st : Nat) : Prog isa :=
  .seq (.block (zero16 st ++ [.li .s8 0]))
    (.ite (.zero .s7) (.block [])
      (.block [.addi .s8 .s7 (-1), .shift .srl .d .s8 .s8 4, .shift .sll .d .s8 .s8 4]))

/-- The arguments of `vg_cmac_aes_update(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`
for the `nb` whole blocks. -/
def cmacArgs₁ (st : Nat) : List Instr := macArgs st ++ [mov .a3 .s6, .shift .srl .d .a4 .s8 4]

/-- The arguments of `vg_cmac_aes_finalize` for the last bytes. -/
def cmacArgs₂ (st : Nat) : List Instr := macArgs st ++ [.add .a3 .s6 .s8, .sub .a4 .s7 .s8]

/-- `AES-CMAC(K1, S)` into the 16 bytes at `W + st`. -/
def cmacOf (st : Nat) : Prog isa :=
  .seq (cmacLen st) (.seq (.block (cmacArgs₁ st)) (.seq updCall (.seq (.block (cmacArgs₂ st)) finCall)))

/-! ## Finishing S2V -/

/-- The short case, `L < 16`: the tail is `pad(P)`, the `L` bytes copied
onto zeros and `0x80` after them; then `dbl(D)`, at `W + 272`, is XORed into
it. -/
def shortTail : Prog isa :=
  .seq (.block (zero16 tailO))
    (.seq (.ite (.zero .s7) (.block [])
        (.seq (.block [mov .a0 .s6, .addi .a1 .s1 (tailO : Int), mov .a2 .s7]) copy))
      (.block (([.add .t0 .s1 .s7, .li .t1 0x80, .store .b .t1 .t0 tailO] : List Instr) ++
        dbl 16 0x87 dO dbO ++ xor16 tailO dbO tailO)))

/-- `16 k` in `s8`: `((L − 1) >> 4) − 1` shifted left by 4, or 0 if that is
negative. -/
def kBlock : Prog isa :=
  .seq (.block [.addi .t0 .s7 (-1), .shift .srl .d .t0 .t0 4, .li .s8 0])
    (.ite (.zero .t0) (.block []) (.block [.addi .t0 .t0 (-1), .shift .sll .d .s8 .t0 4]))

/-- The arguments of `xorBytes` for `D` XORed into the last 16 bytes of the
tail, at `W + 16 + (L − 16 k)`, at any alignment. -/
def xorDArgs : List Instr :=
  [.addi .a0 .s1 (dO : Int), .sub .a1 .s7 .s8, .add .a1 .s1 .a1, .addi .a1 .a1 16, .li .a2 16]

/-- The last `L − 16 k` bytes (at least 16) of the string copied to the
tail, and `D` XORed into its last 16 bytes. -/
def tailCopy : Prog isa :=
  .seq (.block [.add .a0 .s6 .s8, .addi .a1 .s1 (tailO : Int), .sub .a2 .s7 .s8])
    (.seq copy (.seq (.block xorDArgs) xorBytes))

/-- The long case, `L ≥ 16`: `16 k` in `s8`, and the tail. -/
def longTail : Prog isa := .seq kBlock tailCopy

/-- `j` in `s0`: 1 if `L > 16`, else 0. -/
def jBlock : Prog isa :=
  .seq (.block [.addi .t0 .s7 (-1), .shift .srl .d .t0 .t0 4, .li .s0 0])
    (.ite (.zero .t0) (.block []) (.block [.li .s0 1]))

/-- The state at `W + out` zeroed, and the arguments of `vg_cmac_aes_update`
over the `k` blocks of the string. -/
def longArgs₁ (out : Nat) : List Instr :=
  zero16 out ++ macArgs out ++ [mov .a3 .s6, .shift .srl .d .a4 .s8 4]

/-- The arguments of `vg_cmac_aes_update` over the first `j` blocks of the
tail. -/
def longArgs₂ (out : Nat) : List Instr := macArgs out ++ [.addi .a3 .s1 (tailO : Int), mov .a4 .s0]

/-- The arguments of `vg_cmac_aes_finalize` over the rest of the tail. -/
def longArgs₃ (out : Nat) : List Instr :=
  macArgs out ++ [.addi .a3 .s1 (tailO : Int), .shift .sll .d .t0 .s0 4, .add .a3 .a3 .t0, .sub .a4 .s7 .s8,
    .sub .a4 .a4 .t0]

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail, then `vg_cmac_aes_finalize` of
the rest of the tail, into `W + out`. -/
def longMac (out : Nat) : Prog isa :=
  .seq (.block (longArgs₁ out))
    (.seq updCall
      (.seq jBlock (.seq (.block (longArgs₂ out)) (.seq updCall (.seq (.block (longArgs₃ out)) finCall)))))

/-- The state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
def shortArgs (out : Nat) : List Instr :=
  zero16 out ++ macArgs out ++ [.addi .a3 .s1 (tailO : Int), .li .a4 16]

/-- The short case's call: `vg_cmac_aes_finalize` of the tail from a zero
state at `W + out`. -/
def shortMac (out : Nat) : Prog isa := .seq (.block (shortArgs out)) finCall

/-- S2V finished with the string at `s6` (`s7` bytes) from `D` at
`W + 256`, into the 16 bytes at `W + out`. -/
def finish (out : Nat) : Prog isa :=
  .seq (.block [.shift .srl .d .t0 .s7 4])
    (.ite (.zero .t0) (.seq shortTail (shortMac out)) (.seq longTail (longMac out)))

/-! ## CTR -/

/-- The 16 bytes at `W + a` copied to `W + b`. -/
def copy16 (a b : Nat) : List Instr :=
  [.load .d .t0 .s1 a, .store .d .t0 .s1 b, .load .d .t0 .s1 (a + 8), .store .d .t0 .s1 (b + 8)]

/-- The counter `Q` at `W + 64`: the IV at `W + src` with bit 7 of its bytes
8 and 12 cleared, by setting and flipping it (in its second doubleword,
read little-endian, bits 7 and 39). -/
def counter (src : Nat) : List Instr :=
  [.load .d .t0 .s1 src, .store .d .t0 .s1 cntO, .load .d .t0 .s1 (src + 8), .li .t1 0x80,
    .shift .sll .d .t2 .t1 32, .logic .or .t1 .t1 .t2, .logic .or .t0 .t0 .t1, .logic .xor .t0 .t0 .t1,
    .store .d .t0 .s1 (cntO + 8)]

/-- The arguments of `vg_aes_ctr32(schedule = a0, rounds = a1, counter = a2, data = a3, n = a4, scratch = a5)`
but the data and the number of blocks: `K2`'s schedule, the rounds, the
counter block at `W + 96` and the working space. -/
def ctrArgs : List Instr :=
  [.addi .a0 .s2 272, mov .a1 .s3, .addi .a2 .s1 (cbO : Int), .addi .a5 .s1 (scrO : Int)]

/-- `k = ⌊left / 16⌋ mod 2³¹` in `d`: the whole blocks `ctrWhole` does. -/
def wholeCount (d : Reg) : List Instr :=
  [.shift .srl .d d .s7 4, .shift .sll .d d d 33, .shift .srl .d d d 33]

/-- The data and its length in `s6` and `s7`, the counter block `Q`, and
the arguments of `vg_aes_ctr32` over the first `k` whole blocks. -/
def wholePre : List Instr :=
  [mov .s6 .s9, mov .s7 .s10] ++ copy16 cntO cbO ++ wholeCount .a4 ++ ctrArgs ++ [mov .a3 .s6]

/-- The counter `Q + k`, and the data advanced past the `16 k` bytes done.
Only the counter's second doubleword, as a big-endian integer, changes: it
is below `2⁶³` (bit 7 of byte 8 cleared), and the data has fewer than `2⁶⁰`
blocks, so it never carries into the first. -/
def wholePost : List Instr :=
  wholeCount .t0 ++ loadBE64 .t1 .t2 .s1 (cntO + 8) ++ [.add .t1 .t1 .t0] ++ storeBE 8 .t1 .t2 .s1 (cntO + 8) ++
    [.shift .sll .d .t0 .t0 4, .add .s6 .s6 .t0, .sub .s7 .s7 .t0]

/-- The first `k` whole blocks of the data, by one call of `vg_aes_ctr32`
from `Q` (none if `k` is 0). `Q`'s last 32 bits are below `2³¹` and
`k < 2³¹`, so its counter blocks do not wrap around. -/
def ctrWhole : Prog isa := .seq (.block wholePre) (.seq ctrCall (.block wholePost))

/-- The keystream block zeroed, the counter block `Q + i` passed to
`vg_aes_ctr32`, and its arguments for the keystream block. -/
def ctrPre : List Instr :=
  zero16 ksO ++ copy16 cntO cbO ++ ctrArgs ++ [.addi .a3 .s1 (ksO : Int), .li .a4 1]

/-- `min(16, left)` in `a2`, and the keystream block and the data in `a0`
and `a1`. -/
def ctrMin : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s7 4, mov .a2 .s7, .addi .a0 .s1 (ksO : Int), mov .a1 .s6])
    (.ite (.zero .t1) (.block []) (.block [.li .a2 16]))

/-- The counter incremented (its second doubleword, which never carries);
the data advanced past the block. -/
def ctrPost : List Instr :=
  loadBE64 .t1 .t2 .s1 (cntO + 8) ++ [.addi .t1 .t1 1] ++ storeBE 8 .t1 .t2 .s1 (cntO + 8) ++
    [.addi .s6 .s6 16, .shift .srl .d .t0 .s7 4]

/-- The length left reduced by the block's (`min(16, left)`). -/
def ctrLeft : Prog isa := .ite (.zero .t0) (.block [.li .s7 0]) (.block [.addi .s7 .s7 (-16)])

/-- One block of CTR: the first `min(16, left)` bytes of its keystream
XORed into the data. -/
def ctrBody : Prog isa :=
  .seq (.block ctrPre) (.seq ctrCall (.seq ctrMin (.seq xorBytes (.seq (.block ctrPost) ctrLeft))))

/-- The data (`len` bytes at `data`) XORed with the keystream of CTR under
`K2` from the counter `Q` the IV at `W + src` gives: its first `k` whole
blocks by `ctrWhole`, then the rest (the last `len mod 16` bytes, and more
only for data of `2³⁵` bytes or more) a block at a time. -/
def ctr (src : Nat) : Prog isa :=
  .seq (.block (counter src)) (.seq ctrWhole (.ite (.zero .s7) (.block []) (.loop ctrBody (.nonzero .s7))))

/-! ## Comparing the IVs and masking the data -/

/-- `s0 = 1` if the IVs at `W` and `W + 112` are equal, else 0, without a
branch: `1 − (0 < d)` for the OR `d` of the XORs of their doublewords. -/
def compare : List Instr :=
  [.load .d .t0 .s1 0, .load .d .t1 .s1 tO, .logic .xor .t0 .t0 .t1, .load .d .t1 .s1 8,
    .load .d .t2 .s1 (tO + 8), .logic .xor .t1 .t1 .t2, .logic .or .t0 .t0 .t1, .li .t1 0,
    .sltu .t0 .t1 .t0, .li .s0 1, .sub .s0 .s0 .t0]

/-- Every byte of the data ANDed with `0 − s0`: all ones if the IVs are
equal (`s0` is 1), zeros if not. -/
def mask : Prog isa :=
  .seq (.block [.li .t1 0, .sub .t1 .t1 .s0, mov .a0 .s9, mov .a2 .s10])
    (.ite (.zero .a2) (.block []) (.loop (.block maskBody) (.nonzero .a2)))

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

/-- The next component: its address in `s6` and its length in `s7`, from
the descriptor `s4` points to, read little-endian a byte at a time. -/
def adNext : List Instr := loadLE64 .s6 .t0 .t1 .s4 0 ++ loadLE64 .s7 .t0 .t1 .s4 8

/-- `D = dbl(D) XOR` the CMAC state; then the next descriptor, and one
fewer left. -/
def adStep : List Instr :=
  dbl 16 0x87 dO dO ++ xor16 dO stO dO ++ [.addi .s4 .s4 16, .addi .s5 .s5 (-1)]

/-- S2V of the components of associated data, from `D`'s first state. -/
def s2vAds : Prog isa :=
  .ite (.zero .s5) (.block [])
    (.loop (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) (.nonzero .s5))

/-- The data and its length in `s6` and `s7`. -/
def dataStr : List Instr := [mov .s6 .s9, mov .s7 .s10]

/-- The registers' saving, S2V's first state and S2V of the associated data,
then the data as S2V's string. -/
def encS2v : Prog isa :=
  .seq (.block (entry ++ startPre)) (.seq finCall (.seq s2vAds (.block dataStr)))

/-- The synthetic IV at `W` copied to `siv`, a byte at a time. -/
def sivOut : List Instr := copyBytes .t0 .s1 .s11 0 0 16

/-- The received synthetic IV at `siv` copied to `W`, a byte at a time. -/
def sivIn : List Instr := copyBytes .t0 .s11 .s1 0 0 16

/-- Restores the return address and our caller's registers (`s1`, the base,
last). -/
def restore : List Instr := [.load .d .ra .s1 raO] ++ saved.map (fun (r, d) => .load .d r .s1 d)

def encrypt : Prog isa :=
  .seq encS2v (.seq (finish 0) (.seq (ctr 0) (.block (sivOut ++ restore))))

def decrypt : Prog isa :=
  .seq encS2v
    (.seq (.block sivIn) (.seq (ctr 0) (.seq (.block dataStr) (.seq (finish tO)
      (.seq (.block compare) (.seq mask (.block ([mov .a0 .s0] ++ restore))))))))

end VG.Impl.AesSiv.RISCV64
