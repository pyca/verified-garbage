import VerifiedGarbage.Impl.AesGcm.X86
import VerifiedGarbage.Impl.CmacAes.Stream.X86

/-!
# AES-CCM: x86 (32-bit) implementation

`vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, work, tag_len)`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), cdecl (every argument on the stack), composed of calls
of the verified `vg_cmac_aes_update`, whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
from a zero block is CCM's CBC-MAC (§6.1 steps 1–4), and `vg_aes_ctr32`.
Like those, they are generic over the implementation of AES they call
(`c`, and `sfx`, the suffix of the name of `vg_cmac_aes_update` made with
it), and follow the x86-64 implementation (`Impl/AesCcm/X86_64.lean`), with the
conventions and pieces of x86's AES-GCM (`Impl/AesGcm/X86.lean`).

## The working space

`work` (`W`, 2560 bytes):

* `[0, 16)`: the tag (the received one, for `open`);
* `[32, 48)`: a block `B`: `B₀`, the first block of the associated data, or
  a last block padded with zeros;
* `[48, 64)`: the counter block `Ctr₀`;
* `[64, 80)`: the counter block passed to `vg_aes_ctr32`;
* `[80, 96)`: a keystream block;
* `[96, 112)`: the MAC `open` computes;
* `[128, 144)`: our caller's `ebx`, `esi`, `edi`, `ebp`;
* `[144, 184)`: the arguments, kept for the whole function, and whether the
  tags are equal;
* `[196, 212)` and `[240, 256)`: the received tag and the computed one,
  compared (AES-GCM's `recv` and `cmp`, with the received tag at `W` itself,
  whose address is kept at `W + 212`);
* `[272, 284)`: the arguments of the piece running (`dO`, `nO`, `bO`);
* `[384, 2560)`: the working space of the functions called.

## Registers

`ebp` holds `W` throughout; the functions called preserve it. Everything
else is reloaded from `W`. Each call pushes its six arguments (last to
first) in a frame of its own, popped into `eax`: `vg_cmac_aes_update`'s
from `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi` (streaming CMAC's
`call6`), `vg_aes_ctr32`'s from `eax`, `ecx`, `edx`, `ebx`, `edi` and
`ebp` (AES-GCM's), with its working space, `W + 384`, in `ebp`, moved there
before the frame and back after it.

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
* `mac y`: `b0`, `aad` and the payload (`absorbPad` of the data), so that
  `W + y` holds `Yᵣ`.
* `tag y`: `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it.
* `ctr`: the data XORed with the keystream from `Ctr₁`: its whole blocks by
  one call of `vg_aes_ctr32` from `Ctr₁`, which increments only the low 32
  bits of the counter block: as there are fewer than 2²⁸ blocks, they do not
  wrap around; then the last bytes with a keystream block.
* `mask`: every byte of the data ANDed with `0 − ok`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload;
`open` decrypts it, computes the MAC of the plaintext and the tag at
`W + 96`, compares the first `tag_len` bytes of the two tags without a
branch (`recv`, `cmp`), and masks the data.

Only the pointers, `rounds`, the lengths and `tag_len` can affect timing:
the branches are on those, and so are the numbers of calls, bytes copied
and blocks chained.
-/

namespace VG.Impl.AesCcm.X86

open VG.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp saveAt restore keep zero4 copyLoop xorLoop minLen splitWhole
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
abbrev scrO : Nat := 384

/-! ## Calls -/

variable (c : Impl.Aes.X86.Ctr32) (sfx : String)

/-- `vg_aes_ctr32(eax, ecx, edx, ebx, edi, W + 384)`: `ebp` moved to the
callee's working space, the arguments pushed in a frame of their own (as
AES-GCM's `ctrCall`), and `ebp` back. -/
def ctrCall : Prog isa :=
  .seq (.block [.alu .add .ebp (imm scrO)])
    (.seq (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call c.name c.code) (.pop .eax 6))
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

/-- The `nO` bytes at `dO`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block splitWhole)
  (.seq (.ite .e (.block []) (.seq (.block (keyArgs y ++ [.mov .esi (.reg .edi)] ++ updScr)) (updCall c sfx)))
  (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block (zero4 blkO ++ [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
          .mov .ecx (slot nO)]))
        (.seq copyLoop (updBlock c sfx y))))))

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

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (b0 c sfx y)
  (.seq (aad c sfx y)
  (.seq (.block [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp nO) .eax])
    (absorbPad c sfx y)))

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (imm 0)] ++ ctrAt ++ keyArgs c1O ++
      [.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)]))
    (ctrCall c)

/-! ## Counter mode -/

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5): its whole blocks by `vg_aes_ctr32` from `Ctr₁`, then its last
`len mod 16` bytes with a keystream block from `Ctrⱼ`, `j = ⌊len / 16⌋ + 1`. -/
def ctr : Prog isa :=
  .seq (.block ([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp nO) .eax] ++ splitWhole))
  (.seq (.ite .e (.block [])
    (.seq (.block ([.mov .eax (imm 1)] ++ ctrAt ++ keyArgs c1O)) (ctrCall c)))
  (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block ([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] ++ ctrAt ++ zero4 ksO ++
          keyArgs c1O ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)]))
      (.seq (ctrCall c)
        (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
          xorLoop))))))

/-! ## Masking the data -/

/-- Every byte of the data ANDed with `0 − ok`. -/
def mask : Prog isa :=
  .seq (.block [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)])
        (.loop (.block [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl,
          .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne)))

/-! ## The functions -/

/-- Our caller's registers saved in `work` (the ninth argument), `ebp :=`
`work`, the arguments kept, and the address of the received tag (`W`
itself) at `W + 212`. -/
def ccmEntry : Prog isa :=
  entry 8 (keep 0 ctxO ++ keep 1 roundsO ++ keep 2 nonceO ++ keep 3 nlenO ++ keep 4 aadO ++ keep 5 alenO ++
    keep 6 dataO ++ keep 7 lenO ++ keep 9 tglO ++ [.store (at_ .ebp tpO) .ebp])

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq ccmEntry (.seq ctrs (.seq (mac c sfx 0) (.seq (tag c 0) (.seq (ctr c) (.block restore)))))

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa :=
  .seq ccmEntry
  (.seq ctrs
  (.seq (ctr c)
  (.seq (mac c sfx uO)
  (.seq (tag c uO)
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .ebp okO) .eax])
  (.seq mask
    (.block ([.mov .eax (slot okO)] ++ restore))))))))))

end VG.Impl.AesCcm.X86
