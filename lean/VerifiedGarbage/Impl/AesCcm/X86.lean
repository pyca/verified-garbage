module

public import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.CmacAes.Stream.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# AES-CCM: x86 (32-bit) implementation

`vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`, which a frame allocating `work` on the stack implements:
`Proof/AesCcm/X86/Frame.lean`), cdecl (every argument on the stack), composed of calls
of the verified `vg_cmac_aes_update`, whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
from a zero block is CCM's CBC-MAC (§6.1 steps 1–4), and `vg_aes_ctr32_to`.
Like those, they are generic over the implementation of AES they call
(`c`, and `sfx`, the suffix of the name of `vg_cmac_aes_update` made with
it), and follow the x86-64 implementation (`Impl/AesCcm/X86_64.lean`), with the
conventions and pieces of x86's AES-GCM (`Impl/AesGcm/X86.lean`).

## The working space

`work` (`W`, 2560 bytes):

* `[0, 16)`: the tag `seal` computes, copied to `tag` at the end;
* `[32, 48)`: a block `B`: `B₀`, the first block of the associated data, or
  a last block padded with zeros;
* `[48, 64)`: the counter block `Ctr₀`;
* `[64, 80)`: the counter block passed to `vg_aes_ctr32_to`;
* `[80, 96)`: a keystream block;
* `[96, 112)`: the MAC `open` computes;
* `[128, 144)`: our caller's `ebx`, `esi`, `edi`, `ebp`;
* `[144, 184)`: the arguments, kept for the whole function, and whether the
  tags are equal;
* `[196, 212)` and `[240, 256)`: the received tag and the computed one,
  compared (AES-GCM's `recv` and `cmp`, with the address of the received tag,
  `tag`, kept at `W + 212`);
* `[272, 284)`: the arguments of the piece running (`dO`, `nO`, `bO`), and
  `[288, 304)`: those of the chunk (`qO`, `mO`, `iO`, `kO`);
* `[384, 2560)`: the working space of the functions called.

## Registers

`ebp` holds `W` throughout; the functions called preserve it. Everything
else is reloaded from `W`. Each call pushes its arguments (last to first)
in a frame of its own, popped into `eax`: `vg_cmac_aes_update`'s six from
`eax`, `ecx`, `edx`, `ebx`, `esi` and `edi` (streaming CMAC's `call6`),
`vg_aes_ctr32_to`'s seven, in place, from `eax`, `ecx`, `edx`, `ebx`, `edi`,
`ebp` and `ebx` again (AES-GCM's), with its working space, `W + 384`, in
`ebp`, moved there before the frame and back after it.

## The pieces

As on x86-64:

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3), for `q = 15 − n`; `ctrAt` makes
  any `Ctrᵢ` from it by ORing `[i]₃₂` into its last 4 bytes (the bytes of
  `[i]₆₄` before them are zero, as `i < 2³²`, and so are the bytes of
  `[i]₃₂` before the last `q`, as `i < 2^(8q)`).
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), likewise from `Ctr₀`, its first
  byte replaced by the flags; then the MAC state at `W + y` zeroed and `B₀`
  chained into it.
* `aad y`: if there is associated data, its first block, the encoding of its
  length (A.2.2, `header`: 2 or 6 bytes, as its length is less than 2³²)
  followed by as many of its bytes as fit (`aadHead`), then the rest
  (`absorbPad`).
* `absorbPad y`: the `nO` bytes at `dO` padded with zeros to whole blocks,
  chained: the whole blocks in one call, then the last bytes in `B`.
* `macPre y`: `b0` and `aad`.
* `data enc y`: the data encrypted (`enc`) or decrypted, with the keystream
  from `Ctr₁`, and the payload chained, so that `W + y` holds `Yᵣ`: the whole
  blocks a chunk at a time, a call of `vg_cmac_aes_update` and one of
  `vg_aes_ctr32_to` each, the payload first or last (`chunk`); then the last
  bytes, the payload's in `B` (`absorbTail`) and the data's with a keystream
  block (`ctrTail`). `vg_aes_ctr32_to` increments only the low 32 bits of the
  counter block: as there are fewer than 2²⁸ blocks, they do not wrap around.
  With AES-NI a chunk is six blocks: the CBC-MAC is a chain of dependent
  rounds, so a CPU that executes out of order runs the counter blocks of the
  chunks around it in between. With other implementations the chunk is all the
  blocks.
* `tag y`: `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32_to` on it.
* `mask`: every byte of the data ANDed with `0 − ok`.

`seal` encrypts the payload and computes its MAC, then the tag, and copies
it to `tag` (`tagOut`); `open` decrypts the data and computes the MAC of the
plaintext, and the tag, at `W + 96`, compares the first `tag_len` bytes of the two tags without a
branch (`recv`, `cmp`), and masks the data.

Only the pointers, `rounds`, the lengths and `tag_len` can affect timing:
the branches are on those, and so are the numbers of calls, bytes copied
and blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesCcm.X86

open VG.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp saveAt restore keep zero4 copyLoop xorLoop maskWords minLen splitWhole
  recv cmp entry Fn tglO rO vO tpO dO nO bO)

/-! ## The working space -/

abbrev blkO : Nat := 32
abbrev c0O : Nat := 48
abbrev c1O : Nat := 64
abbrev ksO : Nat := 80
abbrev uO : Nat := 96
abbrev ctxO : Nat := 144
abbrev roundsO : Nat := 148
abbrev nonceO : Nat := 152
abbrev nlenO : Nat := 156
abbrev aadO : Nat := 160
abbrev alenO : Nat := 164
abbrev dataO : Nat := 168
abbrev lenO : Nat := 172
abbrev okO : Nat := 176
/-- The address of the rest of the data, the whole blocks left in it, the
index of its first counter block, and the blocks of its first chunk. -/
abbrev qO : Nat := 288
abbrev mO : Nat := 292
abbrev iO : Nat := 296
abbrev kO : Nat := 300
abbrev scrO : Nat := 384

/-! ## Calls -/

variable (c : Impl.Aes.X86.Ctr32) (sfx : String)

/-- `vg_aes_ctr32_to(eax, ecx, edx, ebx, edi, W + 384, ebx)`, in place:
`ebp` moved to the callee's working space, the arguments pushed in a frame
of their own (as AES-GCM's `ctrCall`), and `ebp` back. -/
def ctrCall : Prog isa :=
  .seq (.block [.alu .add .ebp (imm scrO)])
    (.seq (.frame (.push [.ebx, .ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call c.name c.code) (.pop .eax 7))
      (.block [.alu .sub .ebp (imm scrO)]))

/-- `vg_cmac_aes_update(eax, ecx, edx, ebx, esi, edi)`, made with `c`. -/
def updCall : Prog isa :=
  Impl.CmacAes.Stream.X86.call6 ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86.update c)

/-- The key schedule and the number of rounds, and `W + y`, into `eax`,
`ecx`, `edx`. -/
def keyArgs (y : Nat) : List Instr :=
  [.mov .eax (slot ctxO), .mov .ecx (slot roundsO), .mov .edx (.reg .ebp), .alu .add .edx (imm y)]

/-- `vg_cmac_aes_update`'s working space, `W + 384`, into `edi`. -/
def updScr : List Instr := [.mov .edi (.reg .ebp), .alu .add .edi (imm scrO)]

/-! ## The CBC-MAC -/

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (keyArgs y ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm blkO), .mov .esi (imm 1)] ++ updScr))
    (updCall c sfx)

/-- The last `nO` bytes (less than 16) at `dO`, padded with zeros in `B` and
chained into the MAC state at `W + y`, if there are any. -/
def absorbTail (y : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block (zero4 blkO ++ [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
          .mov .ecx (slot nO)]))
        (.seq copyLoop (updBlock c sfx y))))

/-- The `nO` bytes at `dO`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block splitWhole)
  (.seq (.ite .e (.block []) (.seq (.block (keyArgs y ++ [.mov .esi (.reg .edi)] ++ updScr)) (updCall c sfx)))
    (absorbTail c sfx y))

/-- `B` zeroed, and the encoding (A.2.2) of the length `nO` (not 0, and less
than 2³²) of the associated data at its start, its length (2 or 6) at `bO`. -/
def header : Prog isa :=
  .seq (.block (zero4 blkO ++ [.mov .eax (slot nO), .alu .cmp .eax (imm 0xff00)]))
  (.ite .b
    (.block [.bswap .eax, .shift .shr .eax 16, .store (at_ .ebp blkO) .eax, .mov .eax (imm 2),
      .store (at_ .ebp bO) .eax])
    (.block [.mov .ecx (imm 0xfeff), .store (at_ .ebp blkO) .ecx, .bswap .eax, .store (at_ .ebp (blkO + 2)) .eax,
      .mov .eax (imm 6), .store (at_ .ebp bO) .eax]))

/-- The first block of the associated data (`nO` bytes at `dO`, at least
one): the encoding of its length followed by its first `min (16 − h, nO)`
bytes, padded with zeros, chained into `W + y`; `dO` and `nO` then the
rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq minLen
  (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax])
  (.seq copyLoop (updBlock c sfx y))))

/-- The associated data, formatted (A.2.2) and chained into `W + y`. -/
def aad (y : Nat) : Prog isa :=
  .seq (.block [.mov .eax (slot aadO), .store (at_ .ebp dO) .eax, .mov .eax (slot alenO),
      .store (at_ .ebp nO) .eax, .alu .test .eax (.reg .eax)])
    (.ite .e (.block []) (.seq (aadHead c sfx y) (absorbPad c sfx y)))

/-- `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3) at `W + 48`. -/
def ctrs : Prog isa :=
  .seq (.block (zero4 c0O ++ [.mov .eax (imm 14), .alu .sub .eax (slot nlenO), .store8 (at_ .ebp c0O) .al,
      .mov .edi (slot nonceO), .mov .edx (.reg .ebp), .alu .add .edx (imm (c0O + 1)), .mov .ecx (slot nlenO)]))
    copyLoop

/-- The counter block `Ctrᵢ` (A.3), for `i < 2^(8q)` in `eax`, at `W + 64`:
`Ctr₀` with `[i]₃₂` ORed into its last 4 bytes. -/
def ctrAt : List Instr :=
  [.mov .ecx (slot c0O), .store (at_ .ebp c1O) .ecx, .mov .ecx (slot (c0O + 4)), .store (at_ .ebp (c1O + 4)) .ecx,
    .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (c1O + 8)) .ecx, .bswap .eax, .alu .or .eax (slot (c0O + 12)),
    .store (at_ .ebp (c1O + 12)) .eax]

/-- `B₀` (A.2.1) in `B`, from `Ctr₀`: its first byte replaced by the flags
`64 [a > 0] + 8 ((t − 2) / 2) + q − 1` (and `8 ((t − 2) / 2) = 4 (t − 2)`
for the even `t`), and `[p]₃₂` ORed into its last 4 bytes; then the MAC
state at `W + y` zeroed and `B₀` chained into it. -/
def b0 (y : Nat) : Prog isa :=
  .seq (.block [.mov .eax (slot tglO), .alu .sub .eax (imm 2), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .mov .ecx (imm 14), .alu .sub .ecx (slot nlenO), .alu .add .eax (.reg .ecx),
      .mov .ecx (slot alenO), .alu .test .ecx (.reg .ecx)])
  (.seq (.ite .e (.block []) (.block [.alu .add .eax (imm 64)]))
  (.seq (.block ([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
      .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
      .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
      .store (at_ .ebp (blkO + 12)) .eax] ++ zero4 y))
    (updBlock c sfx y)))

/-- The CBC-MAC of the formatted nonce and associated data (§6.1 steps 1–4),
at `W + y`. -/
def macPre (y : Nat) : Prog isa := .seq (b0 c sfx y) (aad c sfx y)

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32_to` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (imm 0)] ++ ctrAt ++ keyArgs c1O ++
      [.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)]))
    (ctrCall c)

/-! ## The data -/

/-- The blocks of a chunk of the data, of the `W + mO` left (not 0): with
AES-NI six while six are left, otherwise all of them; in `esi`. -/
def pick : Prog isa :=
  if Impl.CmacAes.X86.hardware c then
    .seq (.block [.mov .esi (slot mO), .alu .cmp .esi (imm 6)]) (.ite .b (.block []) (.block [.mov .esi (imm 6)]))
  else .block [.mov .esi (slot mO)]

/-- The chunk, `W + kO` blocks at `W + qO`'s address, chained into the MAC
state at `W + y`. -/
def updStep (y : Nat) : Prog isa :=
  .seq (.block (keyArgs y ++ [.mov .ebx (slot qO), .mov .esi (slot kO)] ++ updScr)) (updCall c sfx)

/-- The chunk XORed with the keystream from `Ctrᵢ`, `i` at `W + iO`. -/
def ctrStep : Prog isa :=
  .seq (.block ([.mov .eax (slot iO)] ++ ctrAt ++ keyArgs c1O ++ [.mov .ebx (slot qO), .mov .edi (slot kO)])) (ctrCall c)

/-- On to the next chunk; ZF is set if no block is left. -/
def advance : List Instr :=
  [.mov .eax (slot kO), .mov .ecx (.reg .eax), .alu .add .ecx (slot iO), .store (at_ .ebp iO) .ecx,
    .mov .ecx (.reg .eax), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .alu .add .ecx (slot qO), .store (at_ .ebp qO) .ecx, .mov .ecx (slot mO),
    .alu .sub .ecx (.reg .eax), .store (at_ .ebp mO) .ecx]

/-- A chunk of the data: chained before it is encrypted (`enc`), or after it
is decrypted. -/
def chunk (enc : Bool) (y : Nat) : Prog isa :=
  .seq (pick c)
  (.seq (.block [.store (at_ .ebp kO) .esi])
    (if enc then .seq (updStep c sfx y) (.seq (ctrStep c) (.block advance))
      else .seq (ctrStep c) (.seq (updStep c sfx y) (.block advance))))

/-- The last `len mod 16` bytes of the data, at `dO` (`nO` of them), XORed
with a keystream block from `Ctrⱼ`, `j = ⌊len / 16⌋ + 1`. -/
def ctrTail : Prog isa :=
  .seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block ([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] ++ ctrAt ++ zero4 ksO ++
          keyArgs c1O ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)]))
      (.seq (ctrCall c)
        (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
          xorLoop))))

/-- The whole blocks of the data, a chunk at a time; `dO` and `nO` then the
rest. -/
def dataWhole (enc : Bool) (y : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp nO) .eax] ++ splitWhole))
    (.ite .e (.block [])
      (.seq (.block [.store (at_ .ebp qO) .ebx, .store (at_ .ebp mO) .edi, .mov .eax (imm 1), .store (at_ .ebp iO) .eax])
        (.loop (chunk c sfx enc y) .ne)))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5), and the plaintext, padded with zeros to whole blocks, chained into
the MAC state at `W + y`: the whole blocks, then the last `len mod 16` bytes. -/
def data (enc : Bool) (y : Nat) : Prog isa :=
  .seq (dataWhole c sfx enc y)
    (if enc then .seq (absorbTail c sfx y) (ctrTail c) else .seq (ctrTail c) (absorbTail c sfx y))

/-! ## Masking the data -/

/-- Every byte of the data ANDed with `0 − ok`: 16 at a time, then four at
a time (`maskWords`), then one at a time. -/
def mask : Prog isa :=
  .seq (.block [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)])
        (.seq maskWords
          (.seq (.block [.alu .test .ecx (.reg .ecx)])
            (.ite .e (.block [])
              (.loop (.block [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl,
                .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne))))))

/-! ## The functions -/

/-- The first `tag_len` bytes of the tag at `W` copied to `tag` (kept at
`W + tpO`). -/
def tagOut : Prog isa :=
  .seq (.block [.mov .edi (.reg .ebp), .mov .edx (slot tpO), .mov .ecx (slot tglO)]) copyLoop

/-- Our caller's registers saved in `work` (the eleventh argument), `ebp :=`
`work`, and the arguments kept (`tag` at `W + 212`). -/
def ccmEntry : Prog isa :=
  entry 10 (keep 0 ctxO ++ keep 1 roundsO ++ keep 2 nonceO ++ keep 3 nlenO ++ keep 4 aadO ++ keep 5 alenO ++
    keep 6 dataO ++ keep 7 lenO ++ keep 8 tpO ++ keep 9 tglO)

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq ccmEntry (.seq ctrs (.seq (macPre c sfx 0) (.seq (data c sfx true 0) (.seq (tag c 0)
    (.seq tagOut (.block restore))))))

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa :=
  .seq ccmEntry
  (.seq ctrs
  (.seq (macPre c sfx uO)
  (.seq (data c sfx false uO)
  (.seq (tag c uO)
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .ebp okO) .eax])
  (.seq mask
  (.seq (.block [.mov .eax (slot okO)])
    (.block restore))))))))))

end VG.Impl.AesCcm.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.AesCcm.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratch)

/-- `vg_aes_ccm_seal` over the counter-mode function `c`, of the variant `sfx`, as emitted. -/
def «seal» (c : Impl.Aes.X86.Ctr32) (sfx : String) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2668 (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» c sfx))

/-- `vg_aes_ccm_open` over the counter-mode function `c`, of the variant `sfx`, as emitted. -/
def «open» (c : Impl.Aes.X86.Ctr32) (sfx : String) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 2668 (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» c sfx))

end VG.Impl.AesCcm.X86.Fn
