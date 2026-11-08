module

public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit

/-!
# AES-GCM on x86-64: `open` of a ciphertext read from elsewhere

`vg_aes_gcm_open_split` `(ctx = rdi, rounds = rsi, nonce = rdx,
nonce_len = rcx, aad = r8, aad_len = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24], tag_len = [rsp + 32], src = [rsp + 40], src_len = [rsp + 48],
work = [rsp + 56])`,
its working space allocated on the stack by `withStackArgScratch`: `open`'s
body (`openBody`) out of place, which reads the `len` bytes of ciphertext at
`src` and writes the plaintext to `dst`, copying nothing. Its arguments are
`open`'s, in the same places, with `src`, its length (which equals `len`)
and `work` after them. The entry is `open`'s (`oneEntry 56`), with `src`
kept in the slot of the received tag's length (`tlO`) and `len` in that of
the total length (`tlenO`, which `open` sets only in `oneBlocks`). After
`J₀` and the additional data (`oneAad`), `prefix` takes `oneBlocks`' place:

* it decrypts the `⌊len / 16⌋` whole blocks at `src` to `dst` and absorbs
  them, by a call of `vg_aes_gcm_decrypt_blocks_to` (`fToDec`), as
  `seal_split`'s `prefix` encrypts them, from the counter block and the
  accumulator of the state, with `dst`, the number of blocks and its
  working space (`W + bScrO`) passed on the stack; and
* keeps the `len mod 16` bytes left at `src` as the data, with the total
  length left at `tlenO`, as `oneBlocks` leaves them.

Then `tag_len` is kept at `tlO` (`tagLen`), where `open` keeps it. The tag of
the ciphertext is that of the bytes at `src`. If it is right, the bytes left
are decrypted from `src` to the end of `dst` (`oneCryptG` out of place); if
not, nothing is done, with `rax` 0, and the caller zeroes `dst`.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.OpenSplit

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm Callees Fn restore oneEntry oneAad oneTag oneCryptG recv cmp tagLenOk tlenO
  auxO tlO uO lenO dataO openBody)

/-- The entry: `open`'s, with `work` at `[rsp + 56]`, and `src` and `len`
kept at `tlO` and `tlenO`, where `prefix` reads them. -/
def entry : List Instr :=
  oneEntry 56 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .rsp 40)), .store (at_ .r15 tlO) .rax,
    .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 tlenO) .rax] : List Instr)

/-- The `len mod 16` bytes left at `src` after its whole blocks kept as the
data, and their number as its length. -/
def rest : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15), .alu .sub .rax (.reg .rcx),
    .store (at_ .r15 lenO) .rcx, .alu .add .rax (.mem (at_ .r15 tlO)), .store (at_ .r15 dataO) .rax]

/-- The whole blocks at `src` decrypted to `dst` and absorbed by `fToDec`, and
the bytes left at `src` kept as the data. -/
def «prefix» (fToDec : Fn) : Prog isa :=
  .seq (.block SealSplit.preTest)
  (.seq (.ite .e (.block [])
      (.seq (.block SealSplit.preArgs) (.frame (.push [.rax, .r10, .r11]) (.call fToDec.name fToDec.code) (.pop .rax 3))))
    (.block rest))

/-- `tag_len` kept at `tlO`, after `prefix`. -/
def tagLen : List Instr := [.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx]

/-- What takes `oneBlocks`' place out of place: `prefix`, then `tagLen`. -/
abbrev mid (fToDec : Fn) : Prog isa := .seq («prefix» fToDec) (.block tagLen)

/-- `vg_aes_gcm_open_split`, calling `c` and `fToDec`: `openBody` out of
place. -/
def openSplit (c : Callees) (fToDec : Fn) : Prog isa :=
  openBody c entry (mid fToDec) (.block []) (oneCryptG c true)

end VG.Impl.AesGcm.X86_64.OpenSplit
