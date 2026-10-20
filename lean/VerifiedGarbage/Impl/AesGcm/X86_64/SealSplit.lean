module

public import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather
import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.Short

/-!
# AES-GCM on x86-64: `seal` of a plaintext whose prefix is elsewhere

`vg_aes_gcm_seal_split` `(ctx = rdi, rounds = rsi, nonce = rdx,
nonce_len = rcx, aad = r8, aad_len = r9, src = [rsp + 8],
src_len = [rsp + 16], dst = [rsp + 24], len = [rsp + 32], tag = [rsp + 40],
work = [rsp + 48])`, its working space allocated on the stack by
`withStackArgScratch`: `seal`, but for the whole blocks of the data. The
entry keeps `dst` and `len` where `seal` keeps the data and its length, `src`
in the slot of the received tag's length (`tlO`, which only `open` uses) and
`src_len` in that of the total length (`tlenO`, which `oneBlocks` sets).
After `J₀` and the additional data (`oneAad`), `prefix`:

* encrypts the `⌊src_len / 16⌋` whole blocks at `src` to `dst` and absorbs
  them, from the counter block and the accumulator of the state, by a call
  of `fTo` (`vg_aes_gcm_encrypt_blocks_to`), with `dst`, the number of
  blocks and its working space (`W + bScrO`) passed on the stack;
* copies the `src_len mod 16` bytes left at `src` after them to `dst`; and
* keeps `len` at `auxO`, and the data from those bytes on as the data and
  its length.

The data is then all at `dst`, with its first whole blocks already
encrypted and absorbed. `seal`'s whole blocks (`oneBlocks`) and end (`fin`:
`oneCrypt` and `oneTag 0` (`finCalls`), or, for the instances whose `seal`
ends without calls, `Short.finishWith` of their keystream) follow, with the
total length put back (`fixTlen`) where `oneBlocks` keeps the length of what
it encrypts, in a frame of one word: `fTo`'s three stack arguments take a
word more of the stack than the call of `oneBlocks`, so the rest runs a word
lower, with the stack below it as in `seal`. The instances with `seal`'s
short path (`Short.cond`) take it too (`runShort`), with `src` copied to
`dst` first by the gathering's `copy` (`copySrc`).
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.SealSplit

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr Callees Fn save restore tagOut oneAad oneBlocks oneCrypt oneTag copyLoop
  stO roundsO alenO tlenO dataO lenO auxO tlO aadO bScrO)

/-- The entry: `seal`'s (`oneEntry 48`) with the data and its length taken
from `dst` and `len`, and `src` and `src_len` kept at `tlO` and `tlenO`. -/
def entry : List Instr :=
  ([.mov .rax (.mem (at_ .rsp 48))] : List Instr) ++ save .rax ++
    ([.mov .r15 (.reg .rax)] : List Instr) ++ ptr .r14 .r15 stO ++
    ([.mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 aadO) .r8,
      .store (at_ .r15 alenO) .r9, .mov .rax (.mem (at_ .rsp 24)), .store (at_ .r15 dataO) .rax,
      .mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 lenO) .rax,
      .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rax,
      .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 tlenO) .rax, .mov .r12 (.reg .rdx),
      .mov .rbp (.reg .rcx)] : List Instr)

/-- The number of whole blocks at `src` into `rax`, `ZF` if none. -/
def preTest : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]

/-- The arguments of `fTo(ctx, rounds, counter, y, src, n, dst, n, scratch)`
for the `rax` whole blocks at `src`, with `scratch`, `n` and `dst` in `rax`,
`r10` and `r11`, to be pushed. -/
def preArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 tlO)), .mov .r9 (.reg .rax), .mov .r10 (.reg .rax),
      .mov .r11 (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rax .r15 bScrO

/-- The bytes left at `src` after its whole blocks: their number into `rcx`,
`ZF` if none, and their address and that of their copy into `rsi` and
`rdi`. -/
def copyArgs : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
    .alu .sub .rax (.reg .rcx), .mov .rsi (.mem (at_ .r15 tlO)), .alu .add .rsi (.reg .rax),
    .mov .rdi (.mem (at_ .r15 dataO)), .alu .add .rdi (.reg .rax), .alu .test .rcx (.reg .rcx)]

/-- `len` kept at `auxO`, and the data from `16 ⌊src_len / 16⌋` on as the
data and its length. -/
def rest : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15), .alu .sub .rax (.reg .rcx),
    .mov .rcx (.mem (at_ .r15 lenO)), .store (at_ .r15 auxO) .rcx, .alu .sub .rcx (.reg .rax),
    .store (at_ .r15 lenO) .rcx, .alu .add .rax (.mem (at_ .r15 dataO)), .store (at_ .r15 dataO) .rax]

/-- The whole blocks at `src` encrypted to `dst` by `fTo`, the bytes left
copied, and the data from them on kept. -/
def «prefix» (fTo : Fn) : Prog isa :=
  .seq (.block preTest)
  (.seq (.ite .e (.block [])
      (.seq (.block preArgs) (.frame (.push [.rax, .r10, .r11]) (.call fTo.name fTo.code) (.pop .rax 3))))
  (.seq (.block copyArgs)
  (.seq (.ite .e (.block []) copyLoop)
    (.block rest))))

/-! ## In one pass

`prefixN` takes the texts whose first slice holds a whole group of 16 blocks
and that hold more of them than it: the bytes of `src` after its last whole
group copied to `dst`, its groups and then those at `dst` after them are
encrypted and absorbed by one interleaved loop `encN`, inline
(`StitchR.encN` on 256-bit registers, `StitchZHTo.encN` on 512-bit ones),
and the data from the last whole group of the text on is kept for `body`. -/

/-- `CF` if `⌊src_len / 256⌋` is not 0 and less than `⌊len / 256⌋`: their
values less one compared unsigned (`len` is at least `src_len`). -/
def nTest : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .shift .shr .rax 8, .alu .sub .rax (imm 1), .mov .rcx (.mem (at_ .r15 lenO)),
    .shift .shr .rcx 8, .alu .sub .rcx (imm 1), .alu .cmp .rax (.reg .rcx)]

/-- The bytes of `src` after its last whole group, their number into `rcx`
and their address and that of their copy into `rsi` and `rdi`, for the
gathering's `copy`. -/
def nCopyArgs : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .shift .shr .rax 8, .shift .shl .rax 8,
    .alu .sub .rcx (.reg .rax), .mov .rsi (.mem (at_ .r15 tlO)), .alu .add .rsi (.reg .rax),
    .mov .rdi (.mem (at_ .r15 dataO)), .alu .add .rdi (.reg .rax)]

/-- The arguments of `encN`: those of `vg_aes_gcm_encrypt_blocks_to`
for the whole groups at `src` (`r9` blocks), and `dst` and the number of
blocks of the whole groups at `dst` after them in `rbx` and `rbp`. -/
def nArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 tlO)), .mov .r9 (.mem (at_ .r15 tlenO)), .shift .shr .r9 8,
      .shift .shl .r9 4, .mov .r10 (.mem (at_ .r15 dataO)), .mov .rbx (.reg .r10),
      .mov .rbp (.mem (at_ .r15 lenO)), .shift .shr .rbp 8, .shift .shl .rbp 4, .alu .sub .rbp (.reg .r9)] :
      List Instr) ++ ptr .r11 .r15 bScrO

/-- `len` kept at `auxO`, and the data from its last whole group on as the
data and its length. -/
def nRest : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 auxO) .rax, .mov .rcx (.reg .rax), .shift .shr .rax 8,
    .shift .shl .rax 8, .alu .sub .rcx (.reg .rax), .store (at_ .r15 lenO) .rcx, .alu .add .rax (.mem (at_ .r15 dataO)),
    .store (at_ .r15 dataO) .rax]

/-- `prefix fTo`, but in one pass (`encN`) for the texts `nTest` takes. -/
def prefixN (fTo : Fn) (encN : Prog isa) : Prog isa :=
  .seq (.block nTest)
    (.ite .b
      (.seq (.block nCopyArgs) (.seq SealGather.copy (.seq (.block nArgs) (.seq encN (.block nRest)))))
      («prefix» fTo))

/-- The total length put back where `oneBlocks` kept the length of what it
encrypted. -/
def fixTlen : List Instr :=
  [.mov .rax (.mem (at_ .r15 auxO)), .store (at_ .r15 tlenO) .rax]

/-- `seal`'s end with calls: the rest of the data encrypted, and the tag. -/
def finCalls (c : Callees) : Prog isa :=
  .seq (oneCrypt c) (oneTag c 0)

/-- The whole blocks of the data at `dst` and the end `fin`, a word lower. -/
def body (c : Callees) (fin : Prog isa) : Prog isa :=
  .frame (.push [.rax])
    (.seq (oneBlocks c.enc) (.seq (.block fixTlen) fin))
    (.pop .rax 1)

/-- After the entry: the additional data, `prefix`, and `body`. -/
def run (c : Callees) (fTo : Fn) (fin : Prog isa) : Prog isa :=
  .seq (oneAad c) (.seq («prefix» fTo) (body c fin))

/-- `src` copied to `dst`, before the data, by the gathering's `copy`. -/
def copySrc : Prog isa :=
  .seq (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
    SealGather.copy

/-- After the entry, for the instances with `seal`'s short path: `run` but for
the texts the short path takes, which it seals at `dst`, `src` copied there
first. -/
def runShort (c : Callees) (fTo : Fn) (fin : Prog isa) : Prog isa :=
  .seq Short.cond (.ite .e (run c fTo fin) (.seq copySrc Short.sealShort))

/-- `vg_aes_gcm_seal_split`, with `work = [rsp + 48]`, after the entry `mid`
(`run` or `runShort`): the tag computed at `W` and copied to `tag`. -/
def «seal» (mid : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq mid (.seq (.block (tagOut (at_ .rsp 40))) (.block restore)))

end VG.Impl.AesGcm.X86_64.SealSplit
