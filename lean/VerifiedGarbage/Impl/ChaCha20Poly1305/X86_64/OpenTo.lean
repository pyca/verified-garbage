module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared

/-!
# ChaCha20-Poly1305 decryption out of place: x86-64

`vg_chacha20_poly1305_open_to(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, len = r9, dst = [rsp + 8], dst_len = [rsp + 16],
tag = [rsp + 24], work = [rsp + 32])`, with `work` allocated on the stack
by its frame (`scratched`), as `open`'s, runs the code `open` runs after its
entry (`openShared`, or the stitched `Stitch.openStitchedShared`), which
reads the ciphertext at `r11` and writes the plaintext to `r8`, with the tag
and `work` at `rsp + 8` and `rsp + 16`. The calling convention lets no
function write its stack arguments, so `framed` lays out `open`'s entry in
a frame of its own, below `open_to`'s stack arguments: it loads `work`, `tag`
and `dst` (into `rax`, `r10` and `r8`) and copies `src` to `r11`, then pushes
`work`, `tag` and `src`, which leaves `tag` and `work` at `rsp + 8` and
`rsp + 16`, `src` where `open`'s return address would be.

As `open` (`Shared.openCode`), the AVX-512 instances run the AVX2 code with
`vg_chacha20_xor_avx512vl`'s or `vg_chacha20_xor_avx2`'s rounds for the
lengths it is the faster for, and choose before they allocate `work`.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.X86_64.OpenTo

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `work`, `tag` and `dst` into `rax`, `r10` and `r8`, and `src` into
`r11`. -/
def toArgs : List Instr :=
  [.mov .rax (.mem (at_ .rsp 32)), .mov .r10 (.mem (at_ .rsp 24)), .mov .r11 (.reg .r8),
   .mov .r8 (.mem (at_ .rsp 8))]

/-- `body` in a frame laid out as `open`'s entry: `src` (where the return
address would be), then `tag` and `work`, `open`'s stack arguments. -/
def framed (body : Prog isa) : Prog isa :=
  .seq (.block toArgs) (.frame (.push [.rax, .r10, .r11]) body (.pop .r10 3))

/-- The body of the instance calling the implementation `x` of
`vg_chacha20_xor` and `b` of `vg_poly1305_blocks`: the stitched code with the
AVX2 one, as `Shared.body`. -/
def body (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  framed (if b = .avx2 then Stitch.openStitchedShared x .avx2 else openShared x b)

/-- `work` in a frame of its own, wiped after the code: `dst`, `dst_len` and
`tag` copied, the address of `work`, and its 1696 bytes, with 8 bytes unused
at the top that keep `work` 16-byte aligned (as `open`'s, `Shared.framed`). -/
def scratched (c : Prog isa) : Prog isa := StackScratch.X86_64.withStackArgScratchWipedX 1744 3 42 c

/-- `vg_chacha20_poly1305_open_to` of an instance, choosing as `open` does
(`Shared.openCode`). -/
def openToCode (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (.block (Stitch.smallTest (Stitch.openLim x.small.vl)))
    (Code.iteCold .b (scratched (body x.small .avx2)) (scratched (body x .avx512)))
  | .ifma => .seq (.block Stitch.ifmaTest)
    (Code.iteCold .b (scratched (body ChaCha20.X86_64.Callee.avx512vl.small .avx2))
      (scratched (body x .ifma)))
  | b => scratched (body x b)

end VG.Impl.ChaCha20Poly1305.X86_64.OpenTo
