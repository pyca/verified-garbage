module

public import VerifiedGarbage.Impl.CmacAes.Stream.AArch64

/-!
# AES-SIV: AArch64 implementation

`vg_aes_siv_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`,
`vg_aes_siv_encrypt(ctx = x0, rounds = x1, ads = x2, ads_count = x3, data = x4, len = x5, siv = x6, work = x7)`
and `vg_aes_siv_decrypt` with the same arguments (see `VG.Spec.Siv.initContract`
and the others), with the working space (`scratch` or `work`) as a last
argument, which a frame on the stack allocates
(`Impl.StackScratch.AArch64.withStackScratch`), composed of calls of the verified `vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32`. `init` is generic over the implementation of AES it calls
(`Ctr32`, the `ExpandKey` that goes with it, and `sfx`, the suffix of the
names of the CMAC functions made with it); `encrypt` and `decrypt` over the
implementation of `vg_cmac_aes_update` they call (`Update`) and the
implementation of AES that goes with it (`Ctr32`, whose CMAC functions have
the suffix `sfx`).

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239), its
CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`. `init`'s working space (`scratch`, 2560
bytes): `[0, 2176)` the working space of the functions called, `[2176, 2216)`
our caller's callee-saved registers and our return address. `encrypt`'s
and `decrypt`'s (`work`, 2576 bytes): `[0, 16)` the synthetic IV, `[16, 32)` a
zero block, `[32, 64)` the last bytes of S2V's last string (`tail`),
`[64, 80)` the counter `Q + i`, `[80, 96)` a keystream block, `[96, 112)` the
counter block passed to `vg_aes_ctr32`, `[112, 128)` the IV `decrypt`
computes, `[128, 144)` a CMAC state, `[144, 160)` `dbl(D)`, `[160, 248)` our
caller's callee-saved registers and our return address, `[248, 256)` the
address of `siv`, `[256, 2432)` the
working space of the functions called, and `[2560, 2576)` S2V's state `D`.
A call (`bl`) stores nothing in memory, so no stack is used but `init`'s
frame.

`encrypt` and `decrypt` keep the working space in `x19`, the key context in
`x20`, the rounds in `x21`, the string S2V absorbs (a component of
associated data, or the data) in `x22` (`x23` bytes), the next descriptor
and how many are left in `x24` and `x25` while S2V absorbs the associated
data, the data in `x26` (`x27` bytes), and the bytes of whole blocks a CMAC
chains in `x28`, across the calls.

* `init` expands `K1` into the context, derives its subkeys after it and
  expands `K2` after them.
* `encrypt` and `decrypt` start S2V with `D = AES-CMAC(K1, <zero>)`
  (`vg_cmac_aes_finalize` of the zero block from a zero state), then, for
  each component `S` of associated data, compute `AES-CMAC(K1, S)` into the
  CMAC state with `vg_cmac_aes_update` over the whole blocks of `S` but its
  last 1 to 16 bytes and `vg_cmac_aes_finalize` of those (`cmacOf`), and
  replace `D` with `dbl(D)` XOR it.
* `encrypt` then finishes S2V with the plaintext into the IV (`finish`) and
  encrypts the plaintext in place with CTR from the IV with two bits
  cleared, `Q` (`ctr`): one call of `vg_aes_ctr32` from the counter block
  `Q` encrypts the first `k = ⌊len / 16⌋ mod 2³¹` whole blocks (`ctrWhole`),
  and the counter becomes `Q + k` as a 128-bit big-endian integer. As
  `vg_aes_ctr32` increments only the last 32 bits of its counter block, this
  needs them not to wrap around: `Q`'s are below `2³¹`, its bit 31 being one
  of the two cleared, and `k < 2³¹`. Then each block left (the last
  `len mod 16` bytes, and more only for data of `2³⁵` bytes or more),
  `vg_aes_ctr32` on a zero block with the counter block `Q + i` gives the
  keystream, whose first `min(16, left)` bytes are XORed into the data, and
  the counter is incremented as a 128-bit big-endian integer.
  It then copies the IV to `siv` (`sivOut`).
* `decrypt` then copies the IV it is given from `siv` to the working space
  (`sivIn`), decrypts with CTR from it, finishes S2V with the plaintext into
  `[112, 128)`, compares the two IVs without a branch and ANDs the data with
  the mask of the result, a word at a time and then its last bytes one at a
  time.

`finish`, for a string `P` of `L` bytes: if `L < 16`, the tail is
`pad(P) XOR dbl(D)` and its CMAC is that of one complete block; otherwise,
with `nb = ⌊(L − 1) / 16⌋` whole blocks before the last 1 to 16 bytes,
`k = max(nb, 1) − 1` and `j = min(nb, 1)`, the tail is the last
`L − 16 k` bytes of `P` with `D` XORed into its last 16 (`P xorend D`), and
the CMAC chains the `k` blocks of `P`, then the first `j` blocks of the
tail, and finalizes the rest of the tail.

The model has no flags to branch on: the branches are `cbz`/`cbnz`, on the
key length, `ads_count`, `len` and the lengths of the components (or
numbers computed from them). Only the pointers, `rounds`, the key length,
`ads_count`, `len` and where the components of associated data are can
affect timing: the branches are on them, and so are the numbers of calls,
bytes copied and blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesSiv.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Ctr32 ExpandKey)
open VG.Impl.CmacAes.AArch64 (mov)

/-! ## The working space -/

/-- The offset of the working space of the functions called. -/
abbrev csOff : Nat := 256
abbrev zOff : Nat := 16
abbrev tailOff : Nat := 32
abbrev cntOff : Nat := 64
abbrev ksOff : Nat := 80
abbrev cbOff : Nat := 96
abbrev tOff : Nat := 112
abbrev stOff : Nat := 128
abbrev dbOff : Nat := 144
abbrev dOff : Nat := 2560

/-- The calls of the CMAC functions made with `c`. -/
abbrev callUpdate (u : Impl.CmacAes.AArch64.Update) : Prog isa := .call u.name u.code

abbrev callFinalize (c : Ctr32) (sfx : String) : Prog isa :=
  .call ("vg_cmac_aes_finalize" ++ sfx) (Impl.CmacAes.AArch64.finalize c)

/-- The words at `pb + pd` and `qb + qd` XORed into `cb + cd`, through `x9`
and `x10`. -/
def xor2 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr .x .x9 pb pd, .ldr .x .x10 qb qd, .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb cd,
   .ldr .x .x9 pb (pd + 8), .ldr .x .x10 qb (qd + 8), .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb (cd + 8)]

/-- The 16 bytes at `x19 + src` copied to `x19 + dst`, through `x9`. -/
def copy16 (src dst : Nat) : List Instr :=
  [.ldr .x .x9 .x19 src, .str .x .x9 .x19 dst, .ldr .x .x9 .x19 (src + 8), .str .x .x9 .x19 (dst + 8)]

/-- The 16 bytes at `x19 + d` zeroed (`x9` zero). -/
def zero16 (d : Nat) : List Instr := [.movz .x .x9 0 0, .str .x .x9 .x19 d, .str .x .x9 .x19 (d + 8)]

/-! ## `vg_aes_siv_init` -/

/-- The registers saved in the scratch buffer, and where. -/
def initSaved : List (Reg × Nat) :=
  [(.x19, 2176), (.x20, 2184), (.x21, 2192), (.x22, 2200), (.x30, 2208)]

/-- `initSaved` with `x22`, the base, last. -/
def initRestored : List (Reg × Nat) :=
  [(.x19, 2176), (.x20, 2184), (.x21, 2192), (.x30, 2208), (.x22, 2200)]

/-- Saves the registers and keeps the key in `x19`, the half length
(`key_len / 2`) in `x20`, the context in `x21` and the scratch buffer in
`x22`; the arguments of
`vg_aes_expand_key_scratch(key = x0, key_len = x1, schedule = x2, scratch = x3)` for
`K1` are then those but the length. -/
def initPre : List Instr :=
  initSaved.map (fun (r, d) => .str .x r .x3 d) ++
  [mov .x19 .x0, .lsr .x .x20 .x1 1, mov .x21 .x2, mov .x22 .x3, mov .x1 .x20]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = x0, rounds = x1, subkeys = x2, scratch = x3)`,
the rounds `key_len / 8 + 6`. -/
def initMid₁ : List Instr :=
  [mov .x0 .x21, .lsr .x .x1 .x20 2, .addImm .x .x1 .x1 6, .addImm .x .x2 .x21 240, mov .x3 .x22]

/-- The arguments of `vg_aes_expand_key_scratch` for `K2`. -/
def initMid₂ : List Instr :=
  [.add .x .x0 .x19 .x20, mov .x1 .x20, .addImm .x .x2 .x21 272, mov .x3 .x22]

/-- The registers restored, with `x22` (restored last) the scratch buffer. -/
def initPost : List Instr := initRestored.map fun (r, d) => .ldr .x r .x22 d

def init (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block initPre)
    (.seq (.call e.name e.code)
      (.seq (.block initMid₁)
        (.seq (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.AArch64.subkeys c))
          (.seq (.block initMid₂) (.seq (.call e.name e.code) (.block initPost))))))

/-! ## Saving the registers -/

/-- The registers `encrypt` and `decrypt` save in the working space, and
where: our caller's callee-saved registers and our return address, and the
address of `siv` (`x6`), which they read back at the end. -/
def saved : List (Reg × Nat) :=
  [(.x19, 160), (.x20, 168), (.x21, 176), (.x22, 184), (.x23, 192), (.x24, 200), (.x25, 208),
   (.x26, 216), (.x27, 224), (.x28, 232), (.x30, 240), (.x6, 248)]

/-- `saved` with `x19`, the base, last. -/
def restored : List (Reg × Nat) :=
  [(.x20, 168), (.x21, 176), (.x22, 184), (.x23, 192), (.x24, 200), (.x25, 208), (.x26, 216),
   (.x27, 224), (.x28, 232), (.x30, 240), (.x19, 160)]

/-- Restores the registers, with `x19` (restored last) the working space. -/
def restore : List Instr := restored.map fun (r, d) => .ldr .x r .x19 d

/-! ## S2V's first state -/

/-- Saves the registers in the working space and keeps the arguments in
them: the working space in `x19`, the context in `x20`, the rounds in `x21`,
the descriptors of the components and their number in `x24` and `x25`, and
the data in `x26` (`x27` bytes). -/
def encPre : List Instr :=
  saved.map (fun (r, d) => .str .x r .x7 d) ++
  [mov .x19 .x7, mov .x20 .x0, mov .x21 .x1, mov .x24 .x2, mov .x25 .x3, mov .x26 .x4, mov .x27 .x5]

/-- The zero block at `W + 16`, `D` zeroed, and the arguments of
`vg_cmac_aes_finalize(key = x0, rounds = x1, state = x2, last = x3, last_len = x4, scratch = x5)`
for the zero block. -/
def startPre : List Instr :=
  [.movz .x .x9 0 0, .str .x .x9 .x19 zOff, .str .x .x9 .x19 (zOff + 8), .str .x .x9 .x19 dOff,
   .str .x .x9 .x19 (dOff + 8), mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 dOff,
   .addImm .x .x3 .x19 zOff, .movz .x .x4 16 0, .addImm .x .x5 .x19 csOff]

/-! ## The CMAC of a string -/

/-- With the string at `x22` (`x23` bytes): the CMAC state at `x19 + st`
zeroed, `16 nb` in `x28` for the `nb` whole blocks before the last 1 to 16
bytes (none for the empty string), and the arguments of
`vg_cmac_aes_update(schedule = x0, rounds = x1, state = x2, data = x3, n = x4, scratch = x5)`
for them. -/
def cmacPre (st : Nat) : Prog isa :=
  .seq (.block (zero16 st ++ ([.movz .x .x28 0 0] : List Instr)))
    (.seq (.ite (.zero .x .x23) (.block [])
        (.block [.subImm .x .x28 .x23 1, .movz .x .x9 15 0, .logic .and .x .x9 .x28 .x9,
          .sub .x .x28 .x28 .x9]))
      (.block [.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 st, mov .x3 .x22,
        .addImm .x .x5 .x19 csOff]))

/-- The arguments of `vg_cmac_aes_finalize` for the last bytes. -/
def cmacMid (st : Nat) : List Instr :=
  [.add .x .x3 .x22 .x28, .sub .x .x4 .x23 .x28, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 st,
   .addImm .x .x5 .x19 csOff]

/-- `AES-CMAC(K1, S)` into the 16 bytes at `x19 + st`. -/
def cmacOf (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) (st : Nat) : Prog isa :=
  .seq (cmacPre st) (.seq (callUpdate u) (.seq (.block (cmacMid st)) (callFinalize c sfx)))

/-! ## Finishing S2V -/

/-- The `x8` bytes at `x7` copied to `x6`, none if `x8` is 0
(`Impl.CmacAes.Stream.AArch64.copy`). -/
def copy : Prog isa := Impl.CmacAes.Stream.AArch64.copy

/-- The short case, `L < 16`: the tail is `pad(P)`; then `D`, copied to
`x19 + 144` and doubled there, is XORed into it. -/
def shortTail : Prog isa :=
  .seq (.block (zero16 tailOff ++ ([.addImm .x .x6 .x19 tailOff, mov .x7 .x22, mov .x8 .x23] : List Instr)))
    (.seq copy
      (.block (([.add .x .x6 .x19 .x23, .addImm .x .x6 .x6 tailOff, .movz .x .x9 0x80 0, .strb .x9 .x6 0] : List Instr) ++
        copy16 dOff dbOff ++ Impl.CmacAes.AArch64.dbl dbOff dbOff ++ xor2 .x19 .x19 .x19 tailOff dbOff tailOff)))

/-- `16 k` in `x28`: `((L − 1) >> 4) − 1` shifted left by 4, or 0 if that is
negative. -/
def kBlock : Prog isa :=
  .seq (.block [.subImm .x .x9 .x23 1, .lsr .x .x9 .x9 4, .movz .x .x28 0 0])
    (.ite (.zero .x .x9) (.block []) (.block [.subImm .x .x9 .x9 1, .lsl .x .x28 .x9 4]))

/-- The arguments of the copy of the tail: the last `L − 16 k` bytes of the
string to `x19 + 32`. -/
def tailArgs : List Instr := [.addImm .x .x6 .x19 tailOff, .add .x .x7 .x22 .x28, .sub .x .x8 .x23 .x28]

/-- `D` XORed into the last 16 bytes of the tail, at `x19 + 16 + (L − 16 k)`. -/
def tailXor : List Instr := ([.sub .x .x6 .x23 .x28, .add .x .x6 .x19 .x6] : List Instr) ++ xor2 .x6 .x19 .x6 16 dOff 16

/-- The long case, `L ≥ 16`: `16 k` in `x28`; the last `L − 16 k` bytes
copied to the tail; `D` XORed into the last 16 bytes of the tail. -/
def longTail : Prog isa := .seq kBlock (.seq (.block tailArgs) (.seq copy (.block tailXor)))

/-- The state at `x19 + out` zeroed, and the arguments of
`vg_cmac_aes_update` over the `k` blocks of the string. -/
def longArgs₁ (out : Nat) : List Instr :=
  zero16 out ++ ([.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 out, mov .x3 .x22,
    .addImm .x .x5 .x19 csOff] : List Instr)

/-- `j` in `x25`: 1 if `L > 16`, else 0. -/
def jBlock : Prog isa :=
  .seq (.block [.subImm .x .x9 .x23 1, .lsr .x .x9 .x9 4, .movz .x .x25 0 0])
    (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x25 1 0]))

/-- The arguments of `vg_cmac_aes_update` over the first `j` blocks of the
tail. -/
def longArgs₂ (out : Nat) : List Instr :=
  [mov .x4 .x25, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 out, .addImm .x .x3 .x19 tailOff,
   .addImm .x .x5 .x19 csOff]

/-- The arguments of `vg_cmac_aes_finalize` over the rest of the tail. -/
def longArgs₃ (out : Nat) : List Instr :=
  [.lsl .x .x9 .x25 4, .addImm .x .x3 .x19 tailOff, .add .x .x3 .x3 .x9, .sub .x .x4 .x23 .x28,
   .sub .x .x4 .x4 .x9, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 out, .addImm .x .x5 .x19 csOff]

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail, then `vg_cmac_aes_finalize` of
the rest of the tail, into `x19 + out`. -/
def longMac (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block (longArgs₁ out))
    (.seq (callUpdate u)
      (.seq jBlock
        (.seq (.block (longArgs₂ out))
          (.seq (callUpdate u) (.seq (.block (longArgs₃ out)) (callFinalize c sfx))))))

/-- The state at `x19 + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
def shortArgs (out : Nat) : List Instr :=
  zero16 out ++ [mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 out, .addImm .x .x3 .x19 tailOff,
    .movz .x .x4 16 0, .addImm .x .x5 .x19 csOff]

/-- The short case's call: `vg_cmac_aes_finalize` of the tail from a zero
state at `x19 + out`. -/
def shortMac (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block (shortArgs out)) (callFinalize c sfx)

/-- S2V finished with the string at `x22` (`x23` bytes) from `D` at
`x19 + 2560`, into the 16 bytes at `x19 + out`. -/
def finish (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x23 4])
    (.ite (.zero .x .x9) (.seq shortTail (shortMac c sfx out)) (.seq longTail (longMac u c sfx out)))

/-! ## CTR -/

/-- The counter `Q`: the IV at `x19 + src` with bit 7 of its bytes 8 and 12
cleared, at `x19 + 64`. -/
def counter (src : Nat) : List Instr :=
  [.ldr .x .x9 .x19 src, .str .x .x9 .x19 cntOff, .ldr .x .x9 .x19 (src + 8), .movz .x .x10 0x80 0,
   .movk .x .x10 0x80 2, .bicRor .x .x9 .x9 .x10 0, .str .x .x9 .x19 (cntOff + 8)]

/-- The keystream block zeroed, the counter block `Q + i` passed to
`vg_aes_ctr32`, and its arguments: `K2`'s schedule, the rounds, the counter
block, the keystream block, one block and the working space. -/
def ctrPre : List Instr :=
  zero16 ksOff ++ copy16 cntOff cbOff ++
  ([.addImm .x .x0 .x20 272, mov .x1 .x21, .addImm .x .x2 .x19 cbOff, .addImm .x .x3 .x19 ksOff,
   .movz .x .x4 1 0, .addImm .x .x5 .x19 csOff] : List Instr)

/-- `min(16, left)` in `x8`, and the data and the keystream block in `x6` and
`x7`. -/
def ctrMin : Prog isa :=
  .seq (.block [.lsr .x .x9 .x23 4, mov .x8 .x23, mov .x6 .x22, .addImm .x .x7 .x19 ksOff])
    (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x8 16 0]))

/-- The first `x8` bytes of the keystream block at `x7` (`x8` from 1 to 16)
XORed into the data at `x6`, advancing both. -/
def xorBytes : Prog isa :=
  .loop (.block [.ldrb .x9 .x6 0, .ldrb .x10 .x7 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x6 0,
    .addImm .x .x6 .x6 1, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]) (.nonzero .x .x8)

/-- The counter incremented as a 128-bit big-endian integer; the data
advanced past the block. -/
def ctrPost : List Instr :=
  [.ldr .x .x9 .x19 (cntOff + 8), .rev .x9 .x9, .ldr .x .x10 .x19 cntOff, .rev .x10 .x10,
   .movz .x .x11 1 0, .adds .x .x9 .x9 .x11, .movz .x .x11 0 0, .adc .x .x10 .x10 .x11, .rev .x9 .x9,
   .rev .x10 .x10, .str .x .x10 .x19 cntOff, .str .x .x9 .x19 (cntOff + 8),
   .addImm .x .x22 .x22 16, .lsr .x .x9 .x23 4, .movz .x .x10 16 0]

/-- The length left reduced by the block's (`min(16, left)`). -/
def ctrLeft : Prog isa :=
  .ite (.zero .x .x9) (.block [.movz .x .x23 0 0]) (.block [.sub .x .x23 .x23 .x10])

/-- One block of CTR. -/
def ctrBody (c : Ctr32) : Prog isa :=
  .seq (.block ctrPre)
    (.seq (.call c.name c.code) (.seq ctrMin (.seq xorBytes (.seq (.block ctrPost) ctrLeft))))

/-- `k = ⌊left / 16⌋ mod 2³¹` in `d`: the whole blocks `ctrWhole` does. -/
def wholeCount (d : Reg) : List Instr := [.lsr .x d .x23 4, .lsl .x d d 33, .lsr .x d d 33]

/-- The counter block `Q` passed to `vg_aes_ctr32`, and its arguments:
`K2`'s schedule, the rounds, the counter block, the data, `k` blocks and
the working space. -/
def wholePre : List Instr :=
  copy16 cntOff cbOff ++ wholeCount .x4 ++
  ([.addImm .x .x0 .x20 272, mov .x1 .x21, .addImm .x .x2 .x19 cbOff, mov .x3 .x22,
   .addImm .x .x5 .x19 csOff] : List Instr)

/-- With `k` in `x9`: the counter plus `k`, and the data advanced past the
`16 k` bytes done. -/
def wholeAdd : List Instr :=
  [.ldr .x .x10 .x19 (cntOff + 8), .rev .x10 .x10, .ldr .x .x11 .x19 cntOff, .rev .x11 .x11,
   .adds .x .x10 .x10 .x9, .movz .x .x12 0 0, .adc .x .x11 .x11 .x12, .rev .x10 .x10, .rev .x11 .x11,
   .str .x .x11 .x19 cntOff, .str .x .x10 .x19 (cntOff + 8), .lsl .x .x9 .x9 4, .add .x .x22 .x22 .x9,
   .sub .x .x23 .x23 .x9]

/-- `k` again; the counter `Q + k` as a 128-bit big-endian integer; the data
advanced past the `16 k` bytes done. -/
def wholePost : List Instr :=
  wholeCount .x9 ++ wholeAdd

/-- The first `k` whole blocks of the data, by one call of `vg_aes_ctr32`
from `Q` (none if `k` is 0). `Q`'s last 32 bits are below `2³¹` and
`k < 2³¹`, so its counter blocks do not wrap around. -/
def ctrWhole (c : Ctr32) : Prog isa :=
  .seq (.block wholePre) (.seq (.call c.name c.code) (.block wholePost))

/-- The data at `x22` (`x23` bytes) XORed with the keystream of CTR under
`K2` from the counter at `x19 + 64`: its first `k` whole blocks by
`ctrWhole`, then the rest (the last `len mod 16` bytes, and more only for
data of `2³⁵` bytes or more) a block at a time; `x22` and `x23` then back
from `x26` and `x27`. -/
def ctr (c : Ctr32) : Prog isa :=
  .seq (ctrWhole c)
    (.seq (.ite (.zero .x .x23) (.block []) (.loop (ctrBody c) (.nonzero .x .x23)))
      (.block [mov .x22 .x26, mov .x23 .x27]))

/-! ## Comparing the IVs and masking the data -/

/-- `x0 = 1` if the IVs at `x19` and `x19 + 112` are equal, else 0
(`((a − 1) ∧ ¬a) >> 63` for `a` the OR of the XORs of their halves), and the
mask `0 − x0` in `x11`. -/
def compare : List Instr :=
  [.ldr .x .x9 .x19 0, .ldr .x .x10 .x19 tOff, .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 8,
   .ldr .x .x11 .x19 (tOff + 8), .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10,
   .subImm .x .x10 .x9 1, .bicRor .x .x10 .x10 .x9 0, .lsr .x .x0 .x10 63, .movz .x .x11 0 0,
   .sub .x .x11 .x11 .x0]

/-- The data (`x27` bytes at `x26`) ANDed with the mask in `x11`: its
`⌊len / 8⌋` whole words (counted down in `x8`), then its last `len mod 8`
bytes. -/
def maskData : Prog isa :=
  .seq (.block [mov .x6 .x26, .lsr .x .x8 .x27 3])
    (.seq (.ite (.zero .x .x8) (.block [])
        (.loop (.block [.ldr .x .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .str .x .x9 .x6 0,
          .addImm .x .x6 .x6 8, .subImm .x .x8 .x8 1]) (.nonzero .x .x8)))
      (.seq (.block [.lsl .x .x8 .x27 61, .lsr .x .x8 .x8 61])
        (.ite (.zero .x .x8) (.block [])
          (.loop (.block [.ldrb .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .strb .x9 .x6 0,
            .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]) (.nonzero .x .x8)))))

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

/-- The next component: its address in `x22` and its length in `x23`, from
the descriptor `x24` points to. -/
def adNext : List Instr := [.ldr .x .x22 .x24 0, .ldr .x .x23 .x24 8]

/-- `D = dbl(D) XOR` the CMAC state; then the next descriptor, and one
fewer left. -/
def adStep : List Instr :=
  Impl.CmacAes.AArch64.dbl dOff dOff ++ xor2 .x19 .x19 .x19 dOff stOff dOff ++
  ([.addImm .x .x24 .x24 16, .subImm .x .x25 .x25 1] : List Instr)

/-- S2V of the components of associated data, from `D`'s first state. -/
def s2vAds (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  .ite (.zero .x .x25) (.block [])
    (.loop (.seq (.block adNext) (.seq (cmacOf u c sfx stOff) (.block adStep))) (.nonzero .x .x25))

/-- The registers' saving, S2V's first state and S2V of the associated data,
then the data and its length in `x22` and `x23`. -/
def encS2v (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block (encPre ++ startPre))
    (.seq (callFinalize c sfx) (.seq (s2vAds u c sfx) (.block [mov .x22 .x26, mov .x23 .x27])))

/-- The IV, the first 16 bytes of the working space, copied to `siv`, whose
address the save left at `W + 248`, through `x9` and `x10`. -/
def sivOut : List Instr :=
  [.ldr .x .x9 .x19 248, .ldr .x .x10 .x19 0, .str .x .x10 .x9 0, .ldr .x .x10 .x19 8, .str .x .x10 .x9 8]

def encrypt (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (encS2v u c sfx)
    (.seq (finish u c sfx 0)
      (.seq (.block (counter 0)) (.seq (ctr c) (.seq (.block sivOut) (.block restore)))))

/-- The received IV at `siv`, whose address the save left at `W + 248`,
copied to the first 16 bytes of the working space, through `x9` and `x10`. -/
def sivIn : List Instr :=
  [.ldr .x .x9 .x19 248, .ldr .x .x10 .x9 0, .str .x .x10 .x19 0, .ldr .x .x10 .x9 8, .str .x .x10 .x19 8]

/-- `decrypt` from the received IV in the first 16 bytes of the working space
on: CTR, S2V's end, the comparison, the mask and the restore. -/
def openTail (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block (counter 0))
    (.seq (ctr c)
      (.seq (finish u c sfx tOff) (.seq (.block compare) (.seq maskData (.block restore)))))

def decrypt (u : Impl.CmacAes.AArch64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (encS2v u c sfx) (.seq (.block sivIn) (openTail u c sfx))

end VG.Impl.AesSiv.AArch64
