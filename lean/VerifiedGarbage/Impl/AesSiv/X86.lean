import VerifiedGarbage.Impl.AesGcm.X86
import VerifiedGarbage.Impl.CmacAes.Stream.X86
import VerifiedGarbage.Impl.StackScratch.X86

/-!
# AES-SIV: x86 (32-bit) implementation

`vg_aes_siv_init(key, key_len, ctx)`,
`vg_aes_siv_encrypt(ctx, rounds, ads, ads_count, data, len, work)` and
`vg_aes_siv_decrypt` with the same arguments (see `VG.Spec.Siv.initContract`
and the others), cdecl (every argument on the stack), composed of calls of
the verified `vg_aes_expand_key`, `vg_cmac_aes_subkeys`,
`vg_cmac_aes_update`, `vg_cmac_aes_finalize` and `vg_aes_ctr32`. Like those,
they are generic over the implementation of AES they call (`c`, the `e` that
goes with it, and `sfx`, the suffix of the names of the CMAC functions made
with it), and follow the x86-64 implementation (`Impl/AesSiv/X86_64.lean`),
with the conventions of x86's AES-CCM (`Impl/AesCcm/X86.lean`).

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239),
its CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`.

## `init`

`init` keeps its working space on the stack (`withStackScratch`, as AES-CMAC's
streaming `init`): `initCore(key, key_len, ctx, scratch)` expands `K1` into the
context, derives its subkeys after it and expands `K2` after them, with our
caller's `ebx`, `esi`, `edi` and `ebp` saved at `scratch + 2176`.

## The working space of `encrypt` and `decrypt`

`work` (`W`, 2576 bytes):

* `[0, 16)`: the synthetic IV;
* `[16, 32)`: a zero block;
* `[32, 64)`: the last bytes of S2V's last string (`tail`);
* `[64, 80)`: the counter `Q + i`;
* `[80, 96)`: a keystream block;
* `[96, 112)`: the counter block passed to `vg_aes_ctr32`;
* `[112, 128)`: the IV `decrypt` computes;
* `[128, 144)`: our caller's `ebx`, `esi`, `edi`, `ebp`;
* `[144, 160)`: a CMAC state;
* `[160, 176)`: `dbl(D)`;
* `[176, 256)`: the arguments, kept, and the variables of the pieces
  (`ctxO` … `okO`);
* `[256, 2432)`: the working space of the functions called;
* `[2560, 2576)`: S2V's state `D`.

## Registers

`ebp` holds `W` throughout (but in `dbl`, which needs it, and restores it);
the functions called preserve it. Everything else is reloaded from `W`. Each
call pushes its arguments in a frame of its own, popped into `eax`:
`vg_cmac_aes_update`'s and `vg_cmac_aes_finalize`'s from `eax`, `ecx`,
`edx`, `ebx`, `esi` and `edi` (streaming CMAC's `call6`), `vg_aes_ctr32`'s
from `eax`, `ecx`, `edx`, `ebx`, `edi` and `ebp` (AES-GCM's), with its
working space, `W + 256`, in `ebp`, moved there before the frame and back
after it.

## The pieces

As on x86-64:

* `start`: `D = AES-CMAC(K1, <zero>)` (`vg_cmac_aes_finalize` of the zero
  block from a zero state).
* `s2vAds`: for each component `S` of associated data (each descriptor is
  an address and a length, 8 bytes), `AES-CMAC(K1, S)` into the CMAC state
  (`cmacOf`: `vg_cmac_aes_update` over the whole blocks of `S` but its last
  1 to 16 bytes, `vg_cmac_aes_finalize` of those), and `D = dbl(D) XOR` it.
* `finish out`: S2V finished with the string (`strO`, `slenO`) into
  `W + out`: if `L < 16`, the tail is `pad(P) XOR dbl(D)` and its CMAC that of
  one complete block; otherwise, with `nb = ⌊(L − 1) / 16⌋` whole blocks
  before the last 1 to 16 bytes, `k = max(nb, 1) − 1` and `j = min(nb, 1)`,
  the tail is the last `L − 16 k` bytes of `P` with `D` XORed into its last
  16, and the CMAC chains the `k` blocks of `P`, then the first `j` blocks of
  the tail, and finalizes the rest of the tail.
* `counter src`: `Q`, the IV at `W + src` with bit 7 of its bytes 8 and 12
  cleared.
* `ctr`: each block of the data, `vg_aes_ctr32` on a zero block with the
  counter block `Q + i` gives the keystream, whose first `min(16, left)`
  bytes are XORed into the data, and the counter is incremented as a 128-bit
  big-endian integer.
* `compare`, `mask`: `ok = 1` if the IVs at `W` and `W + 112` are equal,
  else 0, without a branch, and every byte of the data ANDed with `0 − ok`.

Only the pointers, `rounds`, the key length, `ads_count`, `len` and where
the components of associated data are can affect timing: the branches are on
them, and so are the numbers of calls, bytes copied and blocks chained.
-/

namespace VG.Impl.AesSiv.X86

open VG.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt restore zero4 copyLoop xorLoop)

/-! ## `vg_aes_siv_init` -/

section
variable (e : Impl.Aes.X86.ExpandKey) (c : Impl.Aes.X86.Ctr32) (sfx : String)

open Impl.CmacAes.Stream.X86 (save call4) in
/-- Saves the registers (at `scratch + 2176`), and the arguments of
`vg_aes_expand_key(key, key_len / 2, ctx, scratch)` for `K1`. -/
def initPre : List Instr :=
  [.mov .eax (argOp 3)] ++ save ++
    [.mov .eax (argOp 0), .mov .ecx (argOp 1), .shift .shr .ecx 1, .mov .edx (argOp 2), .mov .ebx (argOp 3)]

/-- The arguments of `vg_cmac_aes_subkeys(ctx, key_len / 8 + 6, ctx + 240, scratch)`. -/
def initMid₁ : List Instr :=
  [.mov .eax (argOp 2), .mov .ecx (argOp 1), .shift .shr .ecx 3, .alu .add .ecx (imm 6), .mov .edx (.reg .eax),
   .alu .add .edx (imm 240), .mov .ebx (argOp 3)]

/-- The arguments of `vg_aes_expand_key(key + key_len / 2, key_len / 2, ctx + 272, scratch)` for `K2`. -/
def initMid₂ : List Instr :=
  [.mov .ecx (argOp 1), .shift .shr .ecx 1, .mov .eax (argOp 0), .alu .add .eax (.reg .ecx), .mov .edx (argOp 2),
   .alu .add .edx (imm 272), .mov .ebx (argOp 3)]

open Impl.CmacAes.Stream.X86 (call4) in
/-- `initCore(key, key_len, ctx, scratch)`. -/
def initCore : Prog isa :=
  .seq (.block initPre)
    (.seq (call4 e.name e.code)
      (.seq (.block initMid₁)
        (.seq (call4 ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86.subkeys c))
          (.seq (.block initMid₂)
            (.seq (call4 e.name e.code) (.block (Impl.CmacAes.Stream.X86.restore 3)))))))

/-- `vg_aes_siv_init(key, key_len, ctx)`: `initCore` with 2324 bytes of
working space on the stack, its fourth argument. -/
def init : Prog isa := Impl.StackScratch.X86.withStackScratch 2324 3 (initCore e c sfx)

end

/-! ## The working space -/

abbrev zOff : Nat := 16
abbrev tailOff : Nat := 32
abbrev cntOff : Nat := 64
abbrev ksOff : Nat := 80
abbrev cbOff : Nat := 96
abbrev tOff : Nat := 112
abbrev stOff : Nat := 144
abbrev dbOff : Nat := 160
abbrev ctxO : Nat := 176
abbrev roundsO : Nat := 180
abbrev adsO : Nat := 184
abbrev leftO : Nat := 188
abbrev dataO : Nat := 192
abbrev lenO : Nat := 196
/-- The string S2V is on: its address and length. -/
abbrev strO : Nat := 200
abbrev slenO : Nat := 204
/-- `16 nb` (or `16 k`), and `j`. -/
abbrev nbO : Nat := 208
abbrev jO : Nat := 212
abbrev okO : Nat := 216
abbrev csOff : Nat := 256
abbrev dOff : Nat := 2560

/-! ## Calls -/

section
variable (c : Impl.Aes.X86.Ctr32) (sfx : String)

/-- `vg_cmac_aes_update(eax, ecx, edx, ebx, esi, edi)`, made with `c`. -/
def updCall : Prog isa :=
  Impl.CmacAes.Stream.X86.call6 ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86.update c)

/-- `vg_cmac_aes_finalize(eax, ecx, edx, ebx, esi, edi)`, made with `c`. -/
def finCall : Prog isa :=
  Impl.CmacAes.Stream.X86.call6 ("vg_cmac_aes_finalize" ++ sfx) (Impl.CmacAes.X86.finalize c)

/-- `vg_aes_ctr32(eax, ecx, edx, ebx, edi, W + 256)`: `ebp` moved to the
callee's working space, the arguments pushed in a frame of their own, and
`ebp` back. -/
def ctrCall : Prog isa :=
  .seq (.block [.alu .add .ebp (imm csOff)])
    (.seq (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call c.name c.code) (.pop .eax 6))
      (.block [.alu .sub .ebp (imm csOff)]))

/-- The key context and the rounds into `eax` and `ecx`, `W + st` into
`edx`, the working space of the functions called into `edi`. -/
def macArgs (st : Nat) : List Instr :=
  [.mov .eax (slot ctxO), .mov .ecx (slot roundsO), .mov .edx (.reg .ebp), .alu .add .edx (imm st),
   .mov .edi (.reg .ebp), .alu .add .edi (imm csOff)]

/-! ## S2V's first state -/

/-- The zero block at `W + 16`, `D` zeroed, and `vg_cmac_aes_finalize` of the
zero block from a zero state into `D`. -/
def start : Prog isa :=
  .seq (.block (zero4 zOff ++ zero4 dOff ++ macArgs dOff ++
      [.mov .ebx (.reg .ebp), .alu .add .ebx (imm zOff), .mov .esi (imm 16)]))
    (finCall c sfx)

/-! ## The CMAC of a string -/

/-- The CMAC state at `W + st` zeroed, `16 nb` at `W + nbO` for the `nb`
whole blocks before the last 1 to 16 bytes of the string (none for the
empty string), and `vg_cmac_aes_update` over them. -/
def cmacPre (st : Nat) : Prog isa :=
  .seq (.block (zero4 st ++ [.mov .ecx (imm 0), .mov .eax (slot slenO), .alu .test .eax (.reg .eax)]))
    (.seq (.ite .e (.block [])
        (.block [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1), .alu .and .ecx (imm 0xfffffff0)]))
      (.block ([.store (at_ .ebp nbO) .ecx, .mov .esi (.reg .ecx), .shift .shr .esi 4, .mov .ebx (slot strO)] ++
        macArgs st)))

/-- `vg_cmac_aes_finalize` of the last `L − 16 nb` bytes. -/
def cmacMid (st : Nat) : List Instr :=
  [.mov .ebx (slot strO), .alu .add .ebx (slot nbO), .mov .esi (slot slenO), .alu .sub .esi (slot nbO)] ++ macArgs st

/-- `AES-CMAC(K1, S)` into the 16 bytes at `W + st`, for the string `S` at
`W + strO`. -/
def cmacOf (st : Nat) : Prog isa :=
  .seq (cmacPre st) (.seq (updCall c sfx) (.seq (.block (cmacMid st)) (finCall c sfx)))

/-! ## `dbl` -/

/-- `dbl` of the block at `W + o` in place (AES-CMAC's, with `ebx` its base;
it overwrites `ebp`, which is `W` again after it). -/
def dblAt (o : Nat) : List Instr :=
  [.mov .ebx (.reg .ebp), .alu .add .ebx (imm o)] ++ Impl.CmacAes.X86.dbl 0 0 ++
    [.mov .ebp (.reg .ebx), .alu .sub .ebp (imm o)]

/-- The 16 bytes at `W + src` XORed into those at `edx + d`. -/
def xorInto (src d : Nat) : List Instr :=
  [.mov .eax (slot src), .alu .xor .eax (.mem (at_ .edx d)), .store (at_ .edx d) .eax,
   .mov .eax (slot (src + 4)), .alu .xor .eax (.mem (at_ .edx (d + 4))), .store (at_ .edx (d + 4)) .eax,
   .mov .eax (slot (src + 8)), .alu .xor .eax (.mem (at_ .edx (d + 8))), .store (at_ .edx (d + 8)) .eax,
   .mov .eax (slot (src + 12)), .alu .xor .eax (.mem (at_ .edx (d + 12))), .store (at_ .edx (d + 12)) .eax]

/-! ## S2V of the associated data -/

/-- The next component: its address and length at `W + strO` and
`W + slenO`, from the descriptor `W + adsO` points to. -/
def adNext : List Instr :=
  [.mov .eax (slot adsO), .mov .ecx (.mem (at_ .eax 0)), .store (at_ .ebp strO) .ecx,
   .mov .ecx (.mem (at_ .eax 4)), .store (at_ .ebp slenO) .ecx]

/-- `D = dbl(D) XOR` the CMAC state; then the next descriptor, and one fewer
left (ZF set when none is). -/
def adStep : List Instr :=
  dblAt dOff ++ [.mov .edx (.reg .ebp), .alu .add .edx (imm dOff)] ++ xorInto stOff 0 ++
  [.mov .eax (slot adsO), .alu .add .eax (imm 8), .store (at_ .ebp adsO) .eax,
   .mov .eax (slot leftO), .alu .sub .eax (imm 1), .store (at_ .ebp leftO) .eax]

/-- S2V of the components of associated data, from `D`'s first state. -/
def s2vAds : Prog isa :=
  .seq (.block [.mov .eax (slot leftO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.loop (.seq (.block adNext) (.seq (cmacOf c sfx stOff) (.block adStep))) .ne))

/-! ## Finishing S2V -/

/-- The `ecx` bytes at `edi` copied to `edx` (none if `ecx` is 0). -/
def copyN : Prog isa := .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) copyLoop)

/-- The short case, `L < 16`: the tail is `pad(P)`, then `dbl(D)` (computed
at `W + 160`) is XORed into it. -/
def shortTail : Prog isa :=
  .seq (.block (zero4 tailOff ++ zero4 (tailOff + 16) ++
      [.mov .edi (slot strO), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff), .mov .ecx (slot slenO)]))
    (.seq copyN
      (.block ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++ dblAt dbOff ++
        [.mov .edx (.reg .ebp)] ++ xorInto dbOff tailOff)))

/-- The short case's call: `vg_cmac_aes_finalize` of the tail, one complete
block, from a zero state at `W + out`. -/
def shortMac (out : Nat) : Prog isa :=
  .seq (.block (zero4 out ++ macArgs out ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff),
      .mov .esi (imm 16)]))
    (finCall c sfx)

/-- The long case, `L ≥ 16`: `16 k` at `W + nbO`; the last `L − 16 k` bytes
copied to the tail; `D` XORed into the last 16 bytes of the tail. -/
def longTail : Prog isa :=
  .seq (.block [.mov .eax (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)])
    (.seq (.ite .b (.block [])
        (.block [.mov .eax (.reg .ecx), .alu .sub .eax (imm 1), .alu .and .eax (imm 0xfffffff0),
          .alu .sub .eax (imm 16)]))
      (.seq (.block [.store (at_ .ebp nbO) .eax, .mov .edi (slot strO), .alu .add .edi (.reg .eax),
          .alu .sub .ecx (.reg .eax), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff)])
        (.seq copyLoop
          (.block ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] ++
            xorInto dOff (tailOff - 16))))))

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail (`j` is 1 if `L > 16`, else 0),
then `vg_cmac_aes_finalize` of the rest of the tail, into `W + out`. -/
def longMac (out : Nat) : Prog isa :=
  .seq (.block (zero4 out ++ [.mov .esi (slot nbO), .shift .shr .esi 4, .mov .ebx (slot strO)] ++ macArgs out))
    (.seq (updCall c sfx)
      (.seq (.block [.mov .esi (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)])
        (.seq (.ite .b (.block []) (.block [.mov .esi (imm 1)]))
          (.seq (.block ([.store (at_ .ebp jO) .esi, .mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff)] ++
              macArgs out))
            (.seq (updCall c sfx)
              (.seq (.block ([.mov .eax (slot jO), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
                  .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .esi (slot slenO),
                  .alu .sub .esi (slot nbO), .alu .sub .esi (.reg .eax), .mov .ebx (.reg .ebp),
                  .alu .add .ebx (imm tailOff), .alu .add .ebx (.reg .eax)] ++ macArgs out))
                (finCall c sfx)))))))

/-- S2V finished with the string at `W + strO` (`W + slenO` bytes) from `D`,
into the 16 bytes at `W + out`. -/
def finish (out : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (slot slenO), .alu .cmp .ecx (imm 16)])
    (.ite .b (.seq shortTail (shortMac c sfx out)) (.seq longTail (longMac c sfx out)))

/-! ## CTR -/

/-- The counter `Q`: the IV at `W + src` with bit 7 of its bytes 8 and 12
cleared, at `W + 64`. -/
def counter (src : Nat) : List Instr :=
  [.mov .eax (slot src), .store (at_ .ebp cntOff) .eax, .mov .eax (slot (src + 4)),
   .store (at_ .ebp (cntOff + 4)) .eax, .mov .eax (slot (src + 8)), .alu .and .eax (imm 0xffffff7f),
   .store (at_ .ebp (cntOff + 8)) .eax, .mov .eax (slot (src + 12)), .alu .and .eax (imm 0xffffff7f),
   .store (at_ .ebp (cntOff + 12)) .eax]

/-- The keystream block zeroed, the counter block `Q + i` passed to
`vg_aes_ctr32`, and its arguments: `K2`'s schedule, the rounds, the counter
block, the keystream block and one block. -/
def ctrPre : List Instr :=
  zero4 ksOff ++
  [.mov .eax (slot cntOff), .store (at_ .ebp cbOff) .eax, .mov .eax (slot (cntOff + 4)),
   .store (at_ .ebp (cbOff + 4)) .eax, .mov .eax (slot (cntOff + 8)), .store (at_ .ebp (cbOff + 8)) .eax,
   .mov .eax (slot (cntOff + 12)), .store (at_ .ebp (cbOff + 12)) .eax,
   .mov .eax (slot ctxO), .alu .add .eax (imm 272), .mov .ecx (slot roundsO), .mov .edx (.reg .ebp),
   .alu .add .edx (imm cbOff), .mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff), .mov .edi (imm 1)]

/-- `min(16, left)` in `ecx`, and the arguments of the XOR: the data in
`edi`, the keystream in `edx`. -/
def ctrMin : Prog isa :=
  .seq (.block [.mov .ecx (imm 16), .mov .eax (slot slenO), .alu .cmp .eax (.reg .ecx)])
    (.seq (.ite .b (.block [.mov .ecx (.reg .eax)]) (.block []))
      (.block [.mov .edi (slot strO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksOff),
        .store (at_ .ebp nbO) .ecx]))

/-- The counter incremented as a 128-bit big-endian integer; the data
advanced past the block (ZF set when no data is left). -/
def ctrPost : List Instr :=
  [.mov .eax (slot (cntOff + 12)), .bswap .eax, .alu .add .eax (imm 1), .bswap .eax,
   .store (at_ .ebp (cntOff + 12)) .eax,
   .mov .eax (slot (cntOff + 8)), .bswap .eax, .alu .adc .eax (imm 0), .bswap .eax,
   .store (at_ .ebp (cntOff + 8)) .eax,
   .mov .eax (slot (cntOff + 4)), .bswap .eax, .alu .adc .eax (imm 0), .bswap .eax,
   .store (at_ .ebp (cntOff + 4)) .eax,
   .mov .eax (slot cntOff), .bswap .eax, .alu .adc .eax (imm 0), .bswap .eax,
   .store (at_ .ebp cntOff) .eax,
   .mov .eax (slot strO), .alu .add .eax (imm 16), .store (at_ .ebp strO) .eax,
   .mov .eax (slot slenO), .alu .sub .eax (slot nbO), .store (at_ .ebp slenO) .eax]

/-- One block of CTR. -/
def ctrBody : Prog isa :=
  .seq (.block ctrPre) (.seq (ctrCall c) (.seq ctrMin (.seq xorLoop (.block ctrPost))))

/-- The data (`W + strO`, `W + slenO` bytes) XORed with the keystream of CTR
under `K2` from the counter at `W + 64`. -/
def ctr : Prog isa :=
  .seq (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax, .alu .test .eax (.reg .eax)])
    (.ite .e (.block []) (.loop (ctrBody c) .ne))

/-! ## Comparing the IVs and masking the data -/

/-- `ok = 1` at `W + okO` if the IVs at `W` and `W + 112` are equal, else 0
(the OR of the XORs of their words, then `cmp`, `adc` as AES-GCM's
`cmpTail`). -/
def compare : List Instr :=
  [.mov .eax (slot 0), .alu .xor .eax (slot tOff), .mov .ecx (slot 4), .alu .xor .ecx (slot (tOff + 4)),
   .alu .or .eax (.reg .ecx), .mov .ecx (slot 8), .alu .xor .ecx (slot (tOff + 8)), .alu .or .eax (.reg .ecx),
   .mov .ecx (slot 12), .alu .xor .ecx (slot (tOff + 12)), .alu .or .eax (.reg .ecx),
   .alu .cmp .eax (imm 1), .mov .eax (imm 0), .alu .adc .eax (imm 0), .store (at_ .ebp okO) .eax]

/-- Every byte of the data ANDed with `0 − ok`. -/
def mask : Prog isa :=
  .seq (.block [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)])
        (.loop (.block [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl,
          .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne)))

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

/-- Our caller's registers saved in `work` (the seventh argument),
`ebp :=` `work`, and the arguments kept. -/
def sivEntry : Prog isa :=
  entry 6 (keep 0 ctxO ++ keep 1 roundsO ++ keep 2 adsO ++ keep 3 leftO ++ keep 4 dataO ++ keep 5 lenO)

/-- The entry, S2V's first state and S2V of the associated data, and the
data as the string S2V is on. -/
def encS2v : Prog isa :=
  .seq sivEntry
    (.seq (start c sfx)
      (.seq (s2vAds c sfx)
        (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
          .store (at_ .ebp slenO) .eax])))

def encrypt : Prog isa :=
  .seq (encS2v c sfx) (.seq (finish c sfx 0) (.seq (.block (counter 0)) (.seq (ctr c) (.block restore))))

def decrypt : Prog isa :=
  .seq (encS2v c sfx)
    (.seq (.block (counter 0))
      (.seq (ctr c)
        (.seq (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
            .store (at_ .ebp slenO) .eax])
          (.seq (finish c sfx tOff)
            (.seq (.block compare) (.seq mask (.block ([.mov .eax (slot okO)] ++ restore))))))))

end

end VG.Impl.AesSiv.X86
