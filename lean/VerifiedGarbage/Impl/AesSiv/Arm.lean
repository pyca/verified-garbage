import VerifiedGarbage.Impl.AesCcm.Arm

/-!
# AES-SIV: 32-bit ARM implementation

`vg_aes_siv_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`,
`vg_aes_siv_encrypt(ctx = r0, rounds = r1, ads = r2, ads_count = r3, data = [sp], len = [sp + 4], work = [sp + 8])`
and `vg_aes_siv_decrypt` with the same arguments (see `VG.Spec.Siv.initContract`
and the others), composed of calls of the verified `vg_aes_expand_key`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32`, as on AArch64 (`Impl/AesSiv/AArch64.lean`), but for CTR.

`vg_cmac_aes_update`, `vg_cmac_aes_finalize` and `vg_aes_ctr32` take two
arguments on the stack: a frame pushes them (`push {r12, lr}`: the number
of blocks or bytes in `r12` and the working space in `lr`) around each call,
and its pop loads `r12` back. Their own frames use 8 bytes below that, so
`encrypt` and `decrypt` use 16 bytes of stack, and `init` (whose calls take
no stack arguments) 8 bytes below its own frame. The other arguments on the
stack are read with `ldr rX, [sp, #off]` whenever they are needed.

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239), its
CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`. `init`'s working space (`scratch`, 2560
bytes): `[0, 2176)` the working space of the functions called, `[2176, 2196)`
our caller's `r4`–`r6`, `r11` and our return address `lr`. `encrypt`'s and
`decrypt`'s (`work`, `W`, 2576 bytes): `[0, 16)` the synthetic IV, `[16, 32)`
a zero block, `[32, 64)` the last bytes of S2V's last string (`tail`),
`[80, 96)` a keystream block, `[96, 112)` the counter block passed to
`vg_aes_ctr32`, `[112, 128)` the IV `decrypt` computes, `[128, 164)` our
caller's `r4`–`r11` and our return address `lr` (where AES-GCM saves them,
`Impl.AesGcm.Arm.save`), `[176, 192)` a CMAC state, `[192, 208)` `dbl(D)`,
`[256, 2432)` the working space of the functions called,
and `[2560, 2576)` S2V's state `D`.

`encrypt` and `decrypt` keep `W` in `r11`, the key context in `r10` and the
rounds in `r9` throughout; the next descriptor and how many are left in `r8`
and `r7` while S2V absorbs the associated data; the string S2V absorbs (a
component of associated data, or the data) in `r6` (`r5` bytes); and the
bytes of whole blocks a CMAC chains in `r4`. The functions called preserve
them (they are callee-saved).

* `init` expands `K1` into the context, derives its subkeys after it and
  expands `K2` after them.
* `encrypt` and `decrypt` start S2V with `D = AES-CMAC(K1, <zero>)`
  (`vg_cmac_aes_finalize` of the zero block from a zero state), then, for
  each component `S` of associated data, compute `AES-CMAC(K1, S)` into the
  CMAC state with `vg_cmac_aes_update` over the whole blocks of `S` but its
  last 1 to 16 bytes and `vg_cmac_aes_finalize` of those (`cmacOf`), and
  replace `D` with `dbl(D)` XOR it.
* `encrypt` then finishes S2V with the plaintext into the IV (`finish`) and
  encrypts the plaintext with CTR from the IV with two bits cleared, `Q`
  (`ctr`): the whole blocks in one call of `vg_aes_ctr32`, which increments
  only the last 32 bits of the counter block, as a big-endian integer; but
  `Q` clears their most significant bit and `len < 2³²` gives fewer than
  `2²⁸` blocks, so they never wrap around, and the counter is `Q + i`. Then
  `vg_aes_ctr32` on a zero block with the counter it left gives the keystream
  of the last bytes, which are XORed with it.
* `decrypt` then decrypts with CTR from the IV it is given, finishes S2V with
  the plaintext into `[112, 128)`, compares the two IVs without a branch and
  ANDs every byte of the data with the mask of the result.

`finish`, for a string `P` of `L` bytes: if `L < 16`, the tail is
`pad(P) XOR dbl(D)` and its CMAC is that of one complete block; otherwise,
with `nb = ⌊(L − 1) / 16⌋` whole blocks before the last 1 to 16 bytes,
`k = max(nb, 1) − 1` and `j = min(nb, 1)`, the tail is the last
`L − 16 k` bytes of `P` with `D` XORed into its last 16 (`P xorend D`), and
the CMAC chains the `k` blocks of `P`, then the first `j` blocks of the
tail, and finalizes the rest of the tail.

The model branches only on `Z`: the branches are on the key length's
absence (none), `ads_count`, `len` and the lengths of the components (or
numbers computed from them). Only the pointers, `rounds`, the key length,
`ads_count`, `len` and where the components of associated data are can
affect timing: the branches are on them, and so are the numbers of calls,
bytes copied and blocks chained.
-/

namespace VG.Impl.AesSiv.Arm

open VG.Arm
open VG.Impl.AesGcm.Arm (imm addI ctrFrame copyLoop xorLoop save restore)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Impl.AesCcm.Arm (updFrame)

/-! ## The working space -/

abbrev zOff : Nat := 16
abbrev tailOff : Nat := 32
abbrev ksOff : Nat := 80
abbrev cbOff : Nat := 96
abbrev tOff : Nat := 112
abbrev stOff : Nat := 176
abbrev dbOff : Nat := 192
/-- The offset of the working space of the functions called. -/
abbrev csOff : Nat := 256
abbrev dOff : Nat := 2560

/-! ## The calls -/

/-- `vg_cmac_aes_finalize`, with `last_len` in `r12` and the working space in
`lr` pushed as its stack arguments. -/
def finFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_cmac_aes_finalize" Impl.CmacAes.Arm.finalize) (.pop .r12 8)

/-- The 16 bytes at `W + d` zeroed, through `r12`. -/
def zero16 (d : Nat) : List Instr :=
  [.mov .r12 (imm 0), .str .r12 .r11 d, .str .r12 .r11 (d + 4), .str .r12 .r11 (d + 8),
   .str .r12 .r11 (d + 12)]

/-- The arguments every call of a CMAC function shares: the key context, the
rounds, the state at `W + st` and the working space. -/
def macArgs (st : Nat) : List Instr :=
  [mov .r0 .r10, mov .r1 .r9, addI .r2 .r11 st, addI .lr .r11 csOff]

/-! ## `vg_aes_siv_init` -/

/-- The registers `init` saves in the scratch buffer, and where (`r11`, the
base of the restore, last). -/
def initSaved : List (Reg × Nat) :=
  [(.r4, 2176), (.r5, 2180), (.r6, 2184), (.lr, 2192), (.r11, 2188)]

/-- Saves the registers and keeps the key in `r4`, the half length
(`key_len / 2`) in `r5`, the context in `r6` and the scratch buffer in
`r11`; the arguments of
`vg_aes_expand_key(key = r0, key_len = r1, schedule = r2, scratch = r3)` for
`K1` are then those but the length. -/
def initPre : List Instr :=
  initSaved.map (fun (r, d) => .str r .r3 d) ++
  [mov .r4 .r0, .mov .r5 (.shifted .r1 .lsr 1), mov .r6 .r2, mov .r11 .r3, mov .r1 .r5]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`,
the rounds `key_len / 8 + 6`. -/
def initMid₁ : List Instr :=
  [mov .r0 .r6, .mov .r1 (.shifted .r5 .lsr 2), addI .r1 .r1 6, addI .r2 .r6 240, mov .r3 .r11]

/-- The arguments of `vg_aes_expand_key` for `K2`. -/
def initMid₂ : List Instr :=
  [.dp .add .r0 .r4 (.reg .r5), mov .r1 .r5, addI .r2 .r6 272, mov .r3 .r11]

/-- The registers restored, with `r11` (restored last) the scratch buffer. -/
def initPost : List Instr := initSaved.map fun (r, d) => .ldr r .r11 d

def init : Prog isa :=
  .seq (.block initPre)
    (.seq (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey)
      (.seq (.block initMid₁)
        (.seq (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys)
          (.seq (.block initMid₂)
            (.seq (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) (.block initPost))))))

/-! ## S2V's first state -/

/-- Saves the registers in the working space (`[sp + 8]`) and keeps the
arguments in them: `W` in `r11`, the context in `r10`, the rounds in `r9`,
and the descriptors of the components and their number in `r8` and `r7`. -/
def encPre : List Instr :=
  .ldrSp .r12 8 :: save .r12 ++ [mov .r11 .r12, mov .r10 .r0, mov .r9 .r1, mov .r8 .r2, mov .r7 .r3]

/-- The zero block at `W + 16`, `D` zeroed, and the arguments of
`vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`
for the zero block. -/
def startPre : List Instr :=
  zero16 zOff ++ zero16 dOff ++ macArgs dOff ++ [addI .r3 .r11 zOff, .mov .r12 (imm 16)]

/-! ## The CMAC of a string -/

/-- With the string at `r6` (`r5` bytes): the CMAC state at `W + st`
zeroed, `16 nb` in `r4` for the `nb` whole blocks before the last 1 to 16
bytes (none for the empty string), and the arguments of
`vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`
for them. -/
def cmacPre (st : Nat) : Prog isa :=
  .seq (.block (zero16 st ++ [.mov .r4 (imm 0), .cmp .r5 (imm 0)]))
    (.seq (.ite .eq (.block [])
        (.block [.dp .sub .r4 .r5 (imm 1), .mov .r4 (.shifted .r4 .lsr 4), .mov .r4 (.shifted .r4 .lsl 4)]))
      (.block (macArgs st ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])))

/-- The arguments of `vg_cmac_aes_finalize` for the last bytes. -/
def cmacMid (st : Nat) : List Instr :=
  macArgs st ++ [.dp .add .r3 .r6 (.reg .r4), .dp .sub .r12 .r5 (.reg .r4)]

/-- `AES-CMAC(K1, S)` into the 16 bytes at `W + st`. -/
def cmacOf (st : Nat) : Prog isa :=
  .seq (cmacPre st) (.seq updFrame (.seq (.block (cmacMid st)) finFrame))

/-! ## Finishing S2V -/

/-- The short case, `L < 16`: the tail is `pad(P)`, the `L` bytes copied
onto zeros and `0x80` after them; then `dbl(D)`, at `W + 192`, is XORed into
it. -/
def shortTail : Prog isa :=
  .seq (.block (zero16 tailOff ++ [mov .r1 .r6, addI .r2 .r11 tailOff, mov .r3 .r5, .cmp .r5 (imm 0)]))
    (.seq (.ite .eq (.block []) copyLoop)
      (.block ([.dp .add .r2 .r11 (.reg .r5), .mov .r12 (imm 0x80), .strb .r12 .r2 tailOff, mov .r6 .r11] ++
        Impl.CmacAes.Arm.dbl dOff dbOff ++ xor4 .r11 .r11 .r11 tailOff dbOff tailOff)))

/-- `16 k` in `r4`: `((L − 1) >> 4) − 1` shifted left by 4, or 0 if that is
negative. -/
def kBlock : Prog isa :=
  .seq (.block [.dp .sub .r12 .r5 (imm 1), .mov .r12 (.shifted .r12 .lsr 4), .mov .r4 (imm 0),
      .cmp .r12 (imm 0)])
    (.ite .eq (.block []) (.block [.dp .sub .r12 .r12 (imm 1), .mov .r4 (.shifted .r12 .lsl 4)]))

/-- The last `L − 16 k` bytes (at least 16) of the string copied to the
tail, and `D` XORed into its last 16 bytes, at `W + 16 + (L − 16 k)`. -/
def tailCopy : Prog isa :=
  .seq (.block [.dp .add .r1 .r6 (.reg .r4), addI .r2 .r11 tailOff, .dp .sub .r3 .r5 (.reg .r4)])
    (.seq copyLoop
      (.block ([.dp .sub .r0 .r5 (.reg .r4), .dp .add .r0 .r11 (.reg .r0)] ++ xor4 .r0 .r11 .r0 16 dOff 16)))

/-- The long case, `L ≥ 16`: `16 k` in `r4`, and the tail. -/
def longTail : Prog isa := .seq kBlock tailCopy

/-- `j` in `r7`: 1 if `L > 16`, else 0. -/
def jBlock : Prog isa :=
  .seq (.block [.dp .sub .r12 .r5 (imm 1), .mov .r12 (.shifted .r12 .lsr 4), .mov .r7 (imm 0),
      .cmp .r12 (imm 0)])
    (.ite .eq (.block []) (.block [.mov .r7 (imm 1)]))

/-- The state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_update` over the `k` blocks of the string. -/
def longArgs₁ (out : Nat) : List Instr :=
  zero16 out ++ macArgs out ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)]

/-- The arguments of `vg_cmac_aes_update` over the first `j` blocks of the
tail. -/
def longArgs₂ (out : Nat) : List Instr := macArgs out ++ [addI .r3 .r11 tailOff, mov .r12 .r7]

/-- The arguments of `vg_cmac_aes_finalize` over the rest of the tail. -/
def longArgs₃ (out : Nat) : List Instr :=
  macArgs out ++ [addI .r3 .r11 tailOff, .dp .add .r3 .r3 (.shifted .r7 .lsl 4), .dp .sub .r12 .r5 (.reg .r4),
    .dp .sub .r12 .r12 (.shifted .r7 .lsl 4)]

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail, then `vg_cmac_aes_finalize` of
the rest of the tail, into `W + out`. -/
def longMac (out : Nat) : Prog isa :=
  .seq (.block (longArgs₁ out))
    (.seq updFrame
      (.seq jBlock
        (.seq (.block (longArgs₂ out)) (.seq updFrame (.seq (.block (longArgs₃ out)) finFrame)))))

/-- The state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
def shortArgs (out : Nat) : List Instr :=
  zero16 out ++ macArgs out ++ [addI .r3 .r11 tailOff, .mov .r12 (imm 16)]

/-- The short case's call: `vg_cmac_aes_finalize` of the tail from a zero
state at `W + out`. -/
def shortMac (out : Nat) : Prog isa := .seq (.block (shortArgs out)) finFrame

/-- S2V finished with the string at `r6` (`r5` bytes) from `D` at
`W + 2560`, into the 16 bytes at `W + out`. -/
def finish (out : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)])
    (.ite .eq (.seq shortTail (shortMac out)) (.seq longTail (longMac out)))

/-! ## CTR -/

/-- The counter `Q` at `W + 96`: the IV at `W + src` with bit 7 of its bytes
8 and 12 (of its third and fourth words) cleared, by setting and flipping
it. -/
def counter (src : Nat) : List Instr :=
  [.ldr .r0 .r11 src, .str .r0 .r11 cbOff, .ldr .r0 .r11 (src + 4), .str .r0 .r11 (cbOff + 4),
   .ldr .r0 .r11 (src + 8), .dp .orr .r0 .r0 (imm 0x80), .dp .eor .r0 .r0 (imm 0x80),
   .str .r0 .r11 (cbOff + 8),
   .ldr .r0 .r11 (src + 12), .dp .orr .r0 .r0 (imm 0x80), .dp .eor .r0 .r0 (imm 0x80),
   .str .r0 .r11 (cbOff + 12)]

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
`K2`'s schedule, the rounds, the counter block at `W + 96` and the working
space. -/
def ctrArgs : List Instr :=
  [addI .r0 .r10 272, mov .r1 .r9, addI .r2 .r11 cbOff, addI .lr .r11 csOff]

/-- The whole blocks of the data (`r5` bytes at `r6`), by `vg_aes_ctr32`
from the counter block, which it leaves after them. -/
def ctrWhole : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)])
    (.ite .eq (.block []) (.seq (.block (ctrArgs ++ [mov .r3 .r6])) ctrFrame))

/-- The last `r5 mod 16` bytes of the data, XORed with the keystream block of
the counter block. -/
def ctrTail : Prog isa :=
  .seq (.block [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)]))
        (.seq ctrFrame
          (.seq (.block [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4), .dp .add .r2 .r2 (.reg .r6),
            mov .r3 .r4]) xorLoop))))

/-- The data (`len` bytes at `data`, into `r6` and `r5`) XORed with the
keystream of CTR under `K2` from the counter `Q` the IV at `W + src` gives. -/
def ctr (src : Nat) : Prog isa :=
  .seq (.block (counter src ++ [.ldrSp .r6 0, .ldrSp .r5 4]))
    (.seq ctrWhole ctrTail)

/-! ## Comparing the IVs and masking the data -/

/-- Word `k` of the XOR of the two IVs into `d`, through `r2`. -/
def xorW (d : Reg) (k : Nat) : List Instr :=
  [.ldr d .r11 (4 * k), .ldr .r2 .r11 (tOff + 4 * k), .dp .eor d d (.reg .r2)]

/-- `r0 = 1` if the IVs at `W` and `W + 112` are equal, else 0, without a
branch: `a` the OR of the XORs of their words, `1 − ((a | (0 − a)) >> 31)`. -/
def compare : List Instr :=
  xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 2 ++
    [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
    [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
     .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
     .dp .sub .r0 .r1 (.reg .r0)]

/-- Every byte of the data (`r5` of them, at `r6`) ANDed with the mask
`0 − r0`. -/
def maskData : Prog isa :=
  .seq (.block [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [.ldrb .r12 .r6 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r6 0, addI .r6 .r6 1,
        .subs .r5 .r5 (imm 1)]) .ne))

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

/-- The next component: its address in `r6` and its length in `r5`, from
the descriptor `r8` points to. -/
def adNext : List Instr := [.ldr .r6 .r8 0, .ldr .r5 .r8 4]

/-- `D = dbl(D) XOR` the CMAC state; then the next descriptor, and one
fewer left (Z set when none are). -/
def adStep : List Instr :=
  mov .r6 .r11 :: Impl.CmacAes.Arm.dbl dOff dOff ++ xor4 .r11 .r11 .r11 dOff stOff dOff ++
  [addI .r8 .r8 8, .subs .r7 .r7 (imm 1)]

/-- S2V of the components of associated data, from `D`'s first state. -/
def s2vAds : Prog isa :=
  .seq (.block [.cmp .r7 (imm 0)])
    (.ite .eq (.block []) (.loop (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) .ne))

/-- The registers' saving, S2V's first state and S2V of the associated data,
then the data and its length in `r6` and `r5`. -/
def encS2v : Prog isa :=
  .seq (.block (encPre ++ startPre)) (.seq finFrame (.seq s2vAds (.block [.ldrSp .r6 0, .ldrSp .r5 4])))

def encrypt : Prog isa :=
  .seq encS2v (.seq (finish 0) (.seq (ctr 0) (.block restore)))

def decrypt : Prog isa :=
  .seq encS2v
    (.seq (ctr 0)
      (.seq (.block [.ldrSp .r6 0, .ldrSp .r5 4])
        (.seq (finish tOff) (.seq (.block (compare ++ [.ldrSp .r6 0, .ldrSp .r5 4])) (.seq maskData (.block restore))))))

end VG.Impl.AesSiv.Arm
