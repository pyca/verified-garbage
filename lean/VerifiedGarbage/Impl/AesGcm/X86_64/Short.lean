module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ

/-!
# AES-GCM on x86-64: short messages with AVX-512

`seal` and `open` for CPUs with VAES, VPCLMULQDQ, AVX512F and AVX512BW (and
AES-NI, PCLMULQDQ and SSSE3), with a path of their own for the short
messages of TLS and QUIC: a 12-byte nonce, and at most 32 blocks to hash
(the additional data and the text, each padded to whole blocks, and the
lengths block), with some text or more than 16 bytes of additional data,
which needs no call. The others take the path of the other instances
(`Impl.AesGcm.X86_64.seal`, `open`), but for `seal`'s end: after the whole
blocks, the bytes left, the lengths block and the tag take no calls either
(`finish`).

GHASH over the `m` blocks `X₁ … Xₘ` is `Σ Xᵢ · Hᵐ⁺¹⁻ⁱ`, so the short path
computes the powers `H'` … `H'ᵐ'` once (`H'ᵏ = Hᵏ · x⁻¹`, `m'` the multiple
of 4 from `m` to `m + 3`), puts the blocks hashed one after the other in a
buffer `G` after `m' - m` zero blocks, which add nothing, and adds the
products of each group of four blocks with their powers, lane by lane in
512-bit registers, reducing the sum once. The keystream for the counters
`J₀` … `J₀ + m'` is computed in the same way, four blocks at a time, into a
buffer `K`: `K[0]` masks the tag, and `K[1 …]` the text. None of these depends
on another but through `G`, so the CPU overlaps them. The powers are
computed first, in SSE (`vg_ghash_pclmul`'s code), before any 256- or 512-bit
instruction, and everything after them is in VEX or EVEX forms, so that no
SSE instruction runs with the upper halves of the registers in use.

## The working space

The short path uses `W`'s layout (`Impl.AesGcm.X86_64`), and since it calls
nothing, the callees' working space too:

* `[272, 304)`: `na`, `nc`, `m'` and `m' - m` (`naO`, `ncO`, `mpO`, `leadO`),
  where `na` and `nc` are the blocks of the additional data and the text;
* `[512, 1024)`: `G`, the blocks hashed (`gO`);
* `[1024, 1536)`: `K`, the keystream (`kO`);
* `[1536, 2048)`: the powers, four by four: `H'⁴ʲ⁺⁴`, `H'⁴ʲ⁺³`, `H'⁴ʲ⁺²`,
  `H'⁴ʲ⁺¹` at `+ 64 j` (`tbO`), but with a prepared key context, whose
  powers `ghashP` reads where the context holds them.

Only the lengths, the pointers and `rounds` (and for `open`, whether the
tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Short

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr srcB dstB Callees alenO lenO tlenO aadO dataO roundsO tlO uO auxO j012 recv cmp
  tagLenOk tagOut restore oneEntry oneAad oneBlocks oneCrypt oneTag oneUndo)
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly hInv pows)

def naO : Nat := 272
def ncO : Nat := 280
def mpO : Nat := 288
def leadO : Nat := 296
def gO : Nat := 512
def kO : Nat := 1024
def tbO : Nat := 1536

/-! ## The condition -/

/-- `rax = 1` if the short path applies (a 12-byte nonce in `rbp`, at most 32
blocks to hash, and some text or more than 16 bytes of additional data),
`0` otherwise; then `test rax, rax`. The lengths are first checked to be below
512, so that the blocks' count does not wrap. With neither text nor more
than 16 bytes of additional data, the other instances' body is faster:
`al + 17 n` is at least 17 when there is either. Each branch falls through
while the short path may still apply, and jumps to the end once it cannot. -/
def cond : Prog isa :=
  .seq (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)])
  (.seq (.ite .ne (.block [])
      (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .or .rcx (.mem (at_ .r15 lenO)),
          .alu .cmp .rcx (imm 512)])
        (.ite .ae (.block [])
          (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15), .shift .shr .rcx 4,
              .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4,
              .alu .add .rcx (.reg .rdx), .alu .cmp .rcx (imm 32)])
            (.ite .ae (.block [])
              (.seq (.block [.mov .rdx (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rdx), .shift .shl .rcx 4,
                  .alu .add .rcx (.reg .rdx), .alu .add .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)])
                (.ite .b (.block []) (.block [.mov32 .rax (imm 1)]))))))))
    (.block [.alu .test .rax (.reg .rax)]))

/-! ## The pieces -/

/-- The counts, kept in `W`: `na` and `nc`, `m' = 4 ⌈(na + nc + 1) / 4⌉` and
`m' - (na + nc + 1)`. -/
def sizes : List Instr :=
  [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15), .shift .shr .rcx 4, .store (at_ .r15 naO) .rcx,
   .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4, .store (at_ .r15 ncO) .rdx,
   .mov .rax (.reg .rcx), .alu .add .rax (.reg .rdx), .alu .add .rax (imm 1),
   .mov .r8 (.reg .rax), .alu .add .r8 (imm 3), .shift .shr .r8 2, .shift .shl .r8 2, .store (at_ .r15 mpO) .r8,
   .alu .sub .r8 (.reg .rax), .store (at_ .r15 leadO) .r8]

/-- `G` zeroed, through `zmm2`. -/
def zeroG : List Instr :=
  .zop (.zbin .vpxord .xmm2 .xmm2 .xmm2) :: (List.range 8).map fun i => .vmovdqu32Store (at_ .r15 (gO + 64 * i)) .xmm2

/-- The `rcx` bytes at `rsi` copied to `rdi`: 64 at a time (to `r8 = 64 ⌊rcx / 64⌋`, through
`zmm4`, from `r10 = 0`), then the `rcx mod 64` left in one masked move, with the mask
`2 ^ (rcx mod 64) - 1` in `rax` (`shl` takes the count modulo 64). -/
def copyBytes : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6, .alu .cmp .r8 (imm 0)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.vmovdqu32Load .xmm4 srcB, .vmovdqu32Store dstB .xmm4, .alu .add .r10 (imm 64),
        .alu .cmp .r10 (.reg .r8)]) .ne))
    (.block [.mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1), .kLoad8 .rax .xmm4 srcB,
      .kStore8 dstB .rax .xmm4]))

/-- The additional data copied to `G`, after the zero blocks. -/
def copyA : Prog isa :=
  .seq (.block [.mov .rdi (.mem (at_ .r15 leadO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
      .alu .add .rdi (imm gO), .mov .rsi (.mem (at_ .r15 aadO)), .mov .rcx (.mem (at_ .r15 alenO))])
    copyBytes

/-- `rdi` at the text's blocks in `G`: after the zero blocks and the additional data's. -/
def gText : List Instr :=
  [.mov .rdi (.mem (at_ .r15 leadO)), .alu .add .rdi (.mem (at_ .r15 naO)), .shift .shl .rdi 4,
   .alu .add .rdi (.reg .r15), .alu .add .rdi (imm gO)]

/-- The text (the ciphertext, when decrypting) copied to `G`. -/
def copyC : Prog isa :=
  .seq (.block (gText ++ ([.mov .rsi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 lenO))] : List Instr))) copyBytes

/-! ## The ciphertext into `G` by its groups

`copyC` stores the text 64 bytes at a time from where it starts in `G`,
`16 t` bytes in (`t = lead + na`). `ghash` then loads `G` a group of four
blocks at a time, right after those stores; unless `t` is a multiple of 4,
each of its loads spans two of them, and the CPU forwards a load from one
store only: it waits for both to leave the store buffer (on an Intel Xeon
with AVX-512, `open` took 10–15 ns longer from 192 bytes on than with `t`
a multiple of 4). `copyG` stores whole groups of `G` instead, from the one
the text starts in (`P = G + 16 (t - sh)`, `sh = t mod 4`): the bytes of the
first group before the text (the zero blocks and the additional data) loaded
and ORed with the text's first `64 - 16 sh` bytes, which a masked load reads
into the rest of the register; then whole groups of text; then the last
bytes, with zeros after them (which `G` holds there), in one more group. Its
loads of the text start `16 sh` bytes before it, and those of its first and
last groups are masked to the text's bytes. It stores no masked bytes: AMD's
Zen 4 runs masked 512-bit stores slowly. -/

/-- `rdi = P`, `r8 = 16 sh`, `rsi = D - 16 sh` (`D` the text) and
`r9 = E = 16 sh + n`, the bytes from `P` to the text's end. -/
def gArgs : List Instr :=
  [.mov .rdi (.mem (at_ .r15 leadO)), .alu .add .rdi (.mem (at_ .r15 naO)), .mov .r8 (.reg .rdi),
   .alu .and .r8 (imm 3), .alu .sub .rdi (.reg .r8), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
   .alu .add .rdi (imm gO), .shift .shl .r8 4, .mov .rsi (.mem (at_ .r15 dataO)), .alu .sub .rsi (.reg .r8),
   .mov .r9 (.mem (at_ .r15 lenO)), .alu .add .r9 (.reg .r8)]

/-- The first group: the text's first `64 - 16 sh` bytes, read into bytes
`16 sh` on of `zmm4` through the mask `-1 << 16 sh` (the others zero), ORed
with the group (`zmm6`), and stored; then `r10 = 64` and `r8 = 64 ⌊E / 64⌋`. -/
def gHead : List Instr :=
  [.mov .rcx (.reg .r8), .mov .rax (.imm (BitVec.ofNat 32 0xFFFFFFFF)), .shiftCl .shl .rax,
   .kLoad8 .rax .xmm4 (at_ .rsi 0), .vmovdqu32Load .xmm6 (at_ .rdi 0), .zop (.zbin .vporq .xmm4 .xmm4 .xmm6),
   .vmovdqu32Store (at_ .rdi 0) .xmm4, .mov32 .r10 (imm 64), .mov .r8 (.reg .r9), .shift .shr .r8 6,
   .shift .shl .r8 6]

/-- A whole group of text, from `rsi + r10` to `rdi + r10`. -/
def gBody : List Instr :=
  [.vmovdqu32Load .xmm4 srcB, .vmovdqu32Store dstB .xmm4, .alu .add .r10 (imm 64), .alu .cmp .r10 (.reg .r8)]

/-- The last group: the `E mod 64` bytes left, through the mask
`2 ^ (E mod 64) - 1`, zeros after them, stored whole. -/
def gTail : List Instr :=
  [.mov .rcx (.reg .r9), .mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1),
   .kLoad8 .rax .xmm4 srcB, .vmovdqu32Store dstB .xmm4]

/-- The text copied to `G` by its groups, for at least 192 bytes of text
(so at least two whole groups after the first). -/
def copyG : Prog isa := .seq (.block (gArgs ++ gHead)) (.seq (.loop (.block gBody) .ne) (.block gTail))

/-- The ciphertext into `G`: by `copyG` from 192 bytes on unless the text
starts at a group (`t` a multiple of 4), otherwise by `copyC`, which on an
Intel Xeon with AVX-512 is as fast or faster there (by up to 10% at 16 to
128 bytes). The branches are on the lengths only. Shorter texts fall
through to `copyC` as before; the longer ones' code is out of line
(`Code.iteCold`), after the function's return. -/
def copyCG : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 192)])
    (Code.iteCold .ae
      (.seq (.block [.mov .rax (.mem (at_ .r15 leadO)), .alu .add .rax (.mem (at_ .r15 naO)), .alu .test .rax (imm 3)])
        (.ite .e copyC copyG))
      copyC)

/-! ## The powers -/

/-- The constants in `xmm0` and `xmm1`, `H'` in `xmm3` from the hash subkey
at `ctx + 240`, and `H'²`–`H'⁴` (`vg_ghash_pclmul`'s code, in SSE). -/
def powSse : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.movdquLoad .xmm7 (at_ .r13 240), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++ hInv ++ pows

/-- `H'⁴`, `H'³`, `H'²`, `H'` in the lanes of `zmm8`, stored at the table's
start (`r11`), and the mask and the reduction constant in every lane of
`zmm0` and `zmm1`. -/
def pow4 : List Instr :=
  [.vop (.vinserti128 .xmm8 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm9 .xmm4 .xmm3 1),
   .zop (.vshufi32x4 .xmm8 .xmm8 .xmm9 0x44), .vmovdqu32Store (at_ .r11 0) .xmm8,
   .vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44),
   .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]

/-- The powers four by four up to `m'` (in `rax`): `H'⁸`–`H'⁵` from `H'⁴`,
`H'¹⁶`–`H'⁹` from `H'⁸`, and `H'³²`–`H'¹⁷` from `H'¹⁶`, each group from the
one 4, 8 or 16 below it (`StitchZ.powLoad`), as far as needed. -/
def powMore : Prog isa :=
  .seq (.block [.alu .cmp .rax (imm 5)])
    (.ite .b (.block [])
      (.seq (.block (([.vbroadcasti32x4 .xmm12 (at_ .r11 0)] : List Instr) ++ Gcm.X86_64.StitchZ.powLoad 64 0 ++
          ([.alu .cmp .rax (imm 9)] : List Instr)))
        (.ite .b (.block [])
          (.seq (.block (([.vbroadcasti32x4 .xmm12 (at_ .r11 64)] : List Instr) ++ (List.range 2).flatMap (Gcm.X86_64.StitchZ.powLoad 128) ++
              ([.alu .cmp .rax (imm 17)] : List Instr)))
            (.ite .b (.block [])
              (.block (.vbroadcasti32x4 .xmm12 (at_ .r11 192) :: (List.range 4).flatMap (Gcm.X86_64.StitchZ.powLoad 256))))))))

/-- The table of powers, at `W + tbO`. -/
def powers : Prog isa :=
  .seq (.block (powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ ([.mov .rax (.mem (at_ .r15 mpO))] : List Instr))) powMore

/-- With a prepared key context (`VG.Spec.Gcm.PreparedPowersRepr`), the
constants in every lane of `zmm0` and `zmm1`: `ghashP` reads the powers from
the context itself. -/
def powersP : Prog isa :=
  .block (Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
    ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44),
      .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr))

/-! ## The keystream -/

/-- The counters `J₀`, `J₀ + 1`, `J₀ + 2`, `J₀ + 3` in the lanes of `zmm14`
(from `J₀` at the state's start), 4 in each lane of `zmm15`, the key
schedule, the number of rounds and the last round key's address in `rdi`,
`rsi` and `r10`, for `VaesZ.aesZ`, `rdx` at `K` and `r9` the groups of four
blocks: `Stitch.setupC` (which also loads `xmm2`, unused here), then the
first half of `StitchZ.setupZ`. -/
def ksSetup : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14), .mov .rcx (.reg .r14)] : List Instr) ++
  ptr .r8 .r15 kO ++ Gcm.X86_64.Stitch.setupC ++
  ([.vop (.vbin .vpaddd .l256 .xmm13 .xmm14 .xmm15), .zop (.vshufi32x4 .xmm14 .xmm14 .xmm13 0x44),
   .vop (.vbin .vpaddd .l256 .xmm15 .xmm15 .xmm15), .zop (.vshufi32x4 .xmm15 .xmm15 .xmm15 0x44),
   .mov .r9 (.mem (at_ .r15 ncO)), .alu .add .r9 (imm 4), .shift .shr .r9 2] : List Instr)

/-- Four keystream blocks, stored at `rdx`, then the next four counters. -/
def ksBody : Prog isa :=
  .seq (.block (Aes.X86_64.VaesZ.ctrsZ .xmm14 .xmm0 .xmm15 [.xmm3]))
    (.seq (Aes.X86_64.VaesZ.aesZ .xmm13 [.xmm3])
      (.block [.vmovdqu32Store (at_ .rdx 0) .xmm3, .alu .add .rdx (imm 64), .alu .sub .r9 (imm 1)]))

/-- The keystream for `J₀` … `J₀ + 4 ⌈(nc + 1) / 4⌉ - 1`, at `W + kO`. -/
def keystream : Prog isa := .seq (.block ksSetup) (.loop ksBody .ne)

/-! ## GHASH -/

/-- The lengths block of `G`, its last: `8 a` and `8 n`, big-endian. -/
def lens : List Instr :=
  [.mov .rdi (.mem (at_ .r15 mpO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15), .alu .add .rdi (imm (gO - 16)),
   .mov .rax (.mem (at_ .r15 alenO)), .shift .shl .rax 3, .bswap .rax, .store (at_ .rdi 0) .rax,
   .mov .rax (.mem (at_ .r15 lenO)), .shift .shl .rax 3, .bswap .rax, .store (at_ .rdi 8) .rax]

/-- The groups of `G` and their powers, for `StitchZ.ghLoad 2` (which reads
at `rdx + 128` and `r11 + 128`): `rdx` 128 bytes before `G`, `r11` 128 bytes
before the powers of its first group, `r9` the groups, and the products
cleared. -/
def ghSetup : List Instr :=
  ptr .rdx .r15 (gO - 128) ++
  ([.mov .r9 (.mem (at_ .r15 mpO)), .shift .shr .r9 2, .mov .r11 (.reg .r9), .shift .shl .r11 6,
   .alu .add .r11 (.reg .r15), .alu .add .r11 (imm (tbO - 192)),
   .zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
   .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)] : List Instr)

/-- A group of four blocks, byte-reversed, times its powers, added to the
products (`StitchZ.ghLoad 2`, which adds rather than writes, without `Y`). -/
def ghBody : List Instr :=
  Gcm.X86_64.StitchZ.ghLoad 2 ++ ([.alu .add .rdx (imm 64), .alu .sub .r11 (imm 64), .alu .sub .r9 (imm 1)] : List Instr)

/-- The groups hashed, then the products reduced and added into `xmm2`
(`StitchZ.fin`). -/
def ghash : Prog isa :=
  .seq (.block ghSetup) (.seq (.loop (.block ghBody) .ne) (.block Gcm.X86_64.StitchZ.fin))

/-- `ghSetup` for a prepared key context: `r11` 128 bytes before the powers
of `G`'s first group in the context (`ctx + 256 + 64 (g - 1)`). -/
def ghSetupP : List Instr :=
  ptr .rdx .r15 (gO - 128) ++
  ([.mov .r9 (.mem (at_ .r15 mpO)), .shift .shr .r9 2, .mov .r11 (.reg .r9), .shift .shl .r11 6,
   .alu .add .r11 (.reg .r13), .alu .add .r11 (imm 64),
   .zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
   .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)] : List Instr)

/-- `StitchZ.ghLoad 2` with the powers from a prepared key context, whose
groups hold them in the table's order swapped by halves: swapped back by
`vshufi32x4` with `0x4E`. -/
def ghLoadP : List Instr :=
  ([.vmovdqu32Load .xmm12 (at_ .r11 128), .zop (.vshufi32x4 .xmm12 .xmm12 .xmm12 0x4E),
   .vmovdqu32Load .xmm7 (at_ .rdx 128), .zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] : List Instr) ++
  Gcm.X86_64.StitchZ.acc .xmm7 .xmm12

/-- `ghBody` with the powers from a prepared key context. -/
def ghBodyP : List Instr :=
  ghLoadP ++ ([.alu .add .rdx (imm 64), .alu .sub .r11 (imm 64), .alu .sub .r9 (imm 1)] : List Instr)

/-- `ghash` with the powers from a prepared key context. -/
def ghashP : Prog isa :=
  .seq (.block ghSetupP) (.seq (.loop (.block ghBodyP) .ne) (.block Gcm.X86_64.StitchZ.fin))

/-- The tag, `GHASH ⊕ K[0]`, at `W + o`. -/
def tagK (o : Nat) : List Instr :=
  [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0), .vmovdquLoad .l128 .xmm3 (at_ .r15 kO),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm3), .vmovdquStore .l128 (at_ .r15 o) .xmm2, .vop .vzeroupper]

/-! ## The text -/

/-- `[rsi + r10]` (the text), `[rdx + r10]` (the keystream after `K[0]`),
`[rdi + r10]` (`G`). -/
def kB : MemOp := { base := .rdx, index := some .r10 }

/-- Eight (if `w`) or four bytes at `[rsi + r10]` XORed with those at
`[rdx + r10]` through `rax`, stored back and, if `g`, at `[rdi + r10]`. -/
def xorWord (g w : Bool) : List Instr :=
  (if w then ([.mov .rax (.mem srcB), .alu .xor .rax (.mem kB), .store srcB .rax] : List Instr) ++
      (if g then [.store dstB .rax] else [])
    else ([.mov32 .rax (.mem srcB), .alu32 .xor .rax (.mem kB), .store32 srcB .rax] : List Instr) ++
      (if g then [.store32 dstB .rax] else [])) ++
  [.alu .add .r10 (imm (if w then 8 else 4))]

/-- The bytes from `r10` to `rcx` at `rsi` XORed with those at `rdx`, one at
a time, and if `g` also stored at `rdi`. -/
def xorBytes (g : Bool) : Prog isa :=
  .loop (.block (([.movzx8 .rax srcB, .movzx8 .r9 kB, .alu .xor .rax (.reg .r9), .store8 srcB .rax] : List Instr) ++
    (if g then [.store8 dstB .rax] else []) ++
    ([.alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)] : List Instr))) .ne

/-- The `rcx` bytes at `rsi` XORed with the keystream at `rdx`, and, if `g`,
also stored at `rdi`: 16 at a time (through `xmm4`), then, of the fewer than
16 left, 8 and 4 at a time (through `rax`) as the bits of `rcx` say, and the
last one at a time; fewer than 4 left go straight to the last loop. -/
def xorText (g : Bool) : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4, .alu .cmp .r8 (imm 0)])
  (.seq (.ite .e (.block [])
      (.loop (.block (([.vmovdquLoad .l128 .xmm4 srcB, .vbinLoad .vpxor .l128 .xmm4 .xmm4 kB,
          .vmovdquStore .l128 srcB .xmm4] : List Instr) ++
          (if g then [.vmovdquStore .l128 dstB .xmm4] else []) ++
          ([.alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .r8)] : List Instr))) .ne))
  (.seq (.block [.alu .test .rcx (imm 15)])
    (.ite .e (.block [])
      (.seq (.block [.alu .test .rcx (imm 12)])
        (.ite .e (xorBytes g)
          (.seq (.block [.alu .test .rcx (imm 8)])
          (.seq (.ite .e (.block []) (.block (xorWord g true)))
          (.seq (.block [.alu .test .rcx (imm 4)])
          (.seq (.ite .e (.block []) (.block (xorWord g false)))
          (.seq (.block [.alu .test .rcx (imm 3)])
            (.ite .e (.block []) (xorBytes g))))))))))))

/-- The arguments of `xorText`: the data, `K[1]`, the text's blocks in `G`
and the length. -/
def textArgs : List Instr :=
  gText ++ ([.mov .rsi (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rdx .r15 (kO + 16) ++ ([.mov .rcx (.mem (at_ .r15 lenO))] : List Instr)

/-! ## `seal` and `open` -/

/-- The short `seal`, with the table of powers from `pw` and GHASH by `gh`
(`powers` and `ghash`, or `powersP` and `ghashP` with a prepared key
context): the ciphertext written to the data and `G`, and the tag at `W`. -/
def sealShort (pw : Prog isa := powers) (gh : Prog isa := ghash) : Prog isa :=
  .seq (.block (j012 ++ sizes))
  (.seq pw
  (.seq (.block zeroG)
  (.seq copyA
  (.seq keystream
  (.seq (.seq (.block textArgs) (xorText true))
  (.seq ghash' (.block (tagK 0))))))))
where ghash' : Prog isa := .seq (.block lens) gh

/-- The ciphertext copied to `G`, its tag at `W + uO`, compared with the
received one (`rbx` its length, at `tlO`): `rax`, kept at `auxO`, 1 if they
are equal and 0 if not, and ZF set if not. -/
def openChk (gh : Prog isa := ghash) : Prog isa :=
  .seq copyCG
  (.seq (.block lens)
  (.seq gh
  (.seq (.block (tagK uO ++ ([.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] : List Instr)))
  (.seq recv
  (.seq (cmp uO)
    (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))

/-- The short `open`, after `tagLenOk` (with `rbx` the tag's length, kept
at `tlO`): the tag compared with the received one (`openChk`), and the data
decrypted only if they are equal; `rax` as `open` returns it. -/
def openShort (pw : Prog isa := powers) (gh : Prog isa := ghash) : Prog isa :=
  .seq (.block (j012 ++ sizes))
  (.seq (.seq pw (.seq (.block zeroG) (.seq copyA (.seq keystream (openChk gh)))))
  (.seq (.ite .e (.block []) (.seq (.block textArgs) (xorText false)))
    (.block [.mov .rax (.mem (at_ .r15 auxO))])))

/-! ## The end of a long `seal`

After `oneBlocks`, the other instances encrypt the `r = len mod 16` bytes
left with a call of `vg_aes_ctr32`, and hash them, the lengths block and the
tag's counter block with calls of `vg_ghash` and `vg_aes_ctr32`, one after
the other. `finish` does it without calls: `H'` and `H'²` in SSE
(`vg_ghash_pclmul`'s code), `J₀` and the counter block encrypted together in
two lanes of `zmm5` into `K` (`K[0]` masks the tag, `K[1]` the bytes left),
the bytes left encrypted in place and copied to `G[0]`, which was zeroed
(`xorText true`), the lengths block at `G[1]`, and then, with `Y` the GHASH
accumulator so far, `Y ← mul(Y ⊕ G[0], H'²) ⊕ mul(G[1], H')` (or
`mul(Y ⊕ G[1], H')` without bytes left), reduced once, and the tag
`Y ⊕ K[0]` at `W` (`tagK 0`). -/

/-- `H'` into `xmm3` and `H'²` into `xmm6`, with the constants in `xmm0` and
`xmm1`. -/
def finPow : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .r13 240), .xop (.bin .pshufb .xmm7 .xmm0)] ++ hInv ++
  Gcm.X86_64.Pclmul.mul .xmm6 .xmm3 .xmm3

/-- `J₀` and the counter block in the first two lanes of `zmm5`, and the key
schedule, the number of rounds and the last round key's address in `rdi`,
`rsi` and `r10`, for `VaesZ.aesZ`. -/
def finCtrs : List Instr :=
  [.vmovdquLoad .l128 .xmm5 (at_ .r14 0), .vmovdquLoad .l128 .xmm7 (at_ .r14 48),
   .vop (.vinserti128 .xmm5 .xmm5 .xmm7 1), .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- The keystream of `J₀` and of the counter block at `K`. -/
def finKs : Prog isa :=
  .seq (.block finCtrs)
    (.seq (Aes.X86_64.VaesZ.aesZ .xmm13 [.xmm5]) (.block [.vmovdqu32Store (at_ .r15 kO) .xmm5, .vop .vzeroupper]))

/-- `G[0]` zeroed, and the arguments of `xorText true` for the bytes left. -/
def finTextArgs : List Instr :=
  [.xop (.bin .pxor .xmm7 .xmm7), .movdquStore (at_ .r15 gO) .xmm7] ++ ptr .rdi .r15 gO ++
  [.mov .rsi (.mem (at_ .r15 dataO))] ++ ptr .rdx .r15 (kO + 16) ++ [.mov .rcx (.mem (at_ .r15 lenO))]

/-- The lengths block at `G[1]`: `8 a` and `8 n`, big-endian. -/
def finLens : List Instr :=
  [.mov .rax (.mem (at_ .r15 alenO)), .shift .shl .rax 3, .bswap .rax, .store (at_ .r15 (gO + 16)) .rax,
   .mov .rax (.mem (at_ .r15 tlenO)), .shift .shl .rax 3, .bswap .rax, .store (at_ .r15 (gO + 24)) .rax]

/-- `Y` (from the state) byte-reversed into `xmm12`. -/
def finY : List Instr := [.movdquLoad .xmm12 (at_ .r14 16), .xop (.bin .pshufb .xmm12 .xmm0)]

/-- With bytes left: `mul(Y ⊕ G[0], H'²) ⊕ mul(G[1], H')` into `xmm2`. -/
def finGh2 : List Instr :=
  finY ++ [.movdquLoad .xmm7 (at_ .r15 gO), .xop (.bin .pshufb .xmm7 .xmm0), .xop (.bin .pxor .xmm7 .xmm12)] ++
  Gcm.X86_64.Pclmul.zero ++ Gcm.X86_64.Pclmul.acc .xmm7 .xmm6 ++
  [.movdquLoad .xmm7 (at_ .r15 (gO + 16)), .xop (.bin .pshufb .xmm7 .xmm0)] ++
  Gcm.X86_64.Pclmul.acc .xmm7 .xmm3 ++ Gcm.X86_64.Pclmul.reduce .xmm2

/-- Without: `mul(Y ⊕ G[1], H')` into `xmm2`. -/
def finGh1 : List Instr :=
  finY ++ [.movdquLoad .xmm7 (at_ .r15 (gO + 16)), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm7 .xmm12)] ++
  Gcm.X86_64.Pclmul.zero ++ Gcm.X86_64.Pclmul.acc .xmm7 .xmm3 ++ Gcm.X86_64.Pclmul.reduce .xmm2

/-- The end of a long `seal`, after `oneBlocks`: the bytes left encrypted
and the tag at `W`, without calls, with the keystream of `J₀` and of the
counter block at `K` from `ks`. -/
def finishWith (ks : Prog isa) : Prog isa :=
  .seq (.block finPow)
  (.seq ks
  (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
    (.ite .e (.block (finLens ++ finGh1 ++ tagK 0))
      (.seq (.block finTextArgs)
        (.seq (xorText true) (.block (finLens ++ finGh2 ++ tagK 0)))))))

/-- `finishWith` the keystream of `finKs`, in two lanes of `zmm5`. -/
def finish : Prog isa := finishWith finKs

/-- `H'` into `xmm3` and `H'²` into `xmm6` from a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`), which keeps them at `ctx + 272` and
`ctx + 256`, with the constants in `xmm0` and `xmm1`. -/
def finPowP : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  [.movdquLoad .xmm3 (at_ .r13 272), .movdquLoad .xmm6 (at_ .r13 256)]

/-- `finishWith ks` with `H'` and `H'²` from a prepared key context
(`finPowP`), for at most 16 bytes left, which `xorText` encrypts in one
block. -/
def finishP (ks : Prog isa) : Prog isa :=
  .seq (.block finPowP)
  (.seq ks
  (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
    (.ite .e (.block (finLens ++ finGh1 ++ tagK 0))
      (.seq (.block finTextArgs)
        (.seq (xorText true) (.block (finLens ++ finGh2 ++ tagK 0)))))))

/-- `J₀` and the counter block in `xmm5` and `xmm7`, and the key schedule,
the number of rounds and the last round key's address in `rdi`, `rsi` and
`r10`, for `AesNi.aes`. -/
def finCtrsA : List Instr :=
  [.movdquLoad .xmm5 (at_ .r14 0), .movdquLoad .xmm7 (at_ .r14 48),
   .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- The keystream of `J₀` and of the counter block at `K`, with AES-NI on
128-bit registers, for the CPUs without AVX-512. -/
def finKsA : Prog isa :=
  .seq (.block finCtrsA)
    (.seq (Aes.X86_64.AesNi.aes [.xmm5, .xmm7])
      (.block [.movdquStore (at_ .r15 kO) .xmm5, .movdquStore (at_ .r15 (kO + 16)) .xmm7]))

variable (c : Callees)

/-- The other instances' body of `seal`, after the entry: the tag at `W`. -/
def sealLong : Prog isa := .seq (oneAad c) (.seq (oneBlocks c.enc) finish)

/-- `seal` with the short path (`cond`), with the table of powers from `pw`
and GHASH by `gh`, or else `lng` (the other instances' body, `sealLong`, by
default). -/
def «seal» (pw : Prog isa := powers) (gh : Prog isa := ghash) (lng : Prog isa := sealLong c) : Prog isa :=
  .seq (.block (oneEntry 32))
    (.seq (.seq cond (.ite .e lng (sealShort pw gh)))
      (.seq (.block (tagOut (at_ .rsp 24))) (.block restore)))

/-- The other instances' body of `open`, after the entry and `tagLenOk`. -/
def openLong : Prog isa :=
  .seq (oneAad c)
  (.seq (oneBlocks c.dec)
  (.seq (oneTag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (oneUndo c) (oneCrypt c))
    (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))

/-- `open` with the short path (`cond`), with the table of powers from `pw`
and GHASH by `gh`, or else `lng` (the other instances' body, `openLong`, by
default). -/
def «open» (pw : Prog isa := powers) (lng : Prog isa := openLong c) (gh : Prog isa := ghash) : Prog isa :=
  .seq (.block (oneEntry 40 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx] : List Instr)))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq cond (.ite .e lng (openShort pw gh))))
    (.block restore)))

end VG.Impl.AesGcm.X86_64.Short
