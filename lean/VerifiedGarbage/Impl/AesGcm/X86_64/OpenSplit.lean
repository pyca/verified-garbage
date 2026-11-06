module

public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit

/-!
# AES-GCM on x86-64: `open` of a ciphertext read from elsewhere

`vg_aes_gcm_open_split` `(ctx = rdi, rounds = rsi, nonce = rdx,
nonce_len = rcx, aad = r8, aad_len = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24], tag_len = [rsp + 32], src = [rsp + 40], src_len = [rsp + 48],
work = [rsp + 56])`,
its working space allocated on the stack by `withStackArgScratch`: `open`
(`Impl.AesGcm.X86_64.open`) of the `len` bytes of ciphertext at `src`, with
the plaintext written to `dst` instead of over the ciphertext. Its arguments
are `open`'s, in the same places, with `src`, its length (which equals `len`) and `work` after them. The
entry is `open`'s (`oneEntry 56`), with `src` kept in the slot of the
received tag's length (`tlO`) and `len` in that of the total length
(`tlenO`, which `open` sets only in `oneBlocks`), as `seal_split`'s entry
keeps `src` and its length. After `J₀` and the additional data
(`oneAad`), `seal_split`'s `prefix` takes `oneBlocks`' place, with
`vg_aes_gcm_decrypt_blocks_to` (`fFrom`) as its call:

* it decrypts the `⌊len / 16⌋` whole blocks at `src` to `dst` and absorbs
  them, from the counter block and the accumulator of the state, with
  `dst`, the number of blocks and its working space (`W + bScrO`) passed on
  the stack;
* copies the `len mod 16` bytes left at `src` after them to `dst`; and
* keeps the data from those bytes on as the data, with the total length
  left at `tlenO`, as `oneBlocks` leaves them.

Then `tag_len` is kept at `tlO` (`tagLen`), where `open` keeps it.

The rest is `open`'s, with the ciphertext left at `dst`, but for a wrong tag:
then the plaintext of the whole blocks is left at `dst`, with `rax` 0 (its
callers zero `dst`), rather than encrypted again (`oneUndo`).
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.OpenSplit

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm Callees Fn restore oneEntry oneAad oneTag oneCrypt recv cmp tagLenOk tlenO
  auxO tlO uO)

/-- The entry: `open`'s, with `work` at `[rsp + 56]`, and `src` and `len`
kept at `tlO` and `tlenO`, where `seal_split`'s `prefix` reads them. -/
def entry : List Instr :=
  oneEntry 56 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .mov .rax (.mem (at_ .rsp 40)), .store (at_ .r15 tlO) .rax,
    .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 tlenO) .rax] : List Instr)

/-- `tag_len` kept at `tlO`, after `prefix`. -/
def tagLen : List Instr := [.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx]

/-- `vg_aes_gcm_open_split`, calling `c` and `fFrom`. -/
def openSplit (c : Callees) (fFrom : Fn) : Prog isa :=
  .seq (.block entry)
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq (oneAad c)
      (.seq (SealSplit.prefix fFrom)
      (.seq (.block tagLen)
      (.seq (oneTag c uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (.block []) (oneCrypt c))
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))))))
    (.block restore)))

end VG.Impl.AesGcm.X86_64.OpenSplit
