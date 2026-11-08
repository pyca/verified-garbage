module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Shared

/-!
# ChaCha20-Poly1305 decryption out of place: x86-64

`vg_chacha20_poly1305_open_to(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, len = r9, dst = [rsp + 8], dst_len = [rsp + 16],
tag = [rsp + 24], work = [rsp + 32])`, with `work` allocated on the stack
by its frame (`scratched`), as `open`'s, calls the function `open` calls
(`Shared.callOpen`: `vg_chacha20_poly1305_open_body*`), which reads the
ciphertext at `r11` and writes the plaintext to `r8`: `toArgs` loads `work`,
`tag` and `dst` (into `rax`, `r10` and `r8`) and copies `src` to `r11`.

As `open` (`Shared.openCode`), the AVX-512 instances call the AVX2 code with
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

/-- The body of the instance calling the implementation `x` of
`vg_chacha20_xor` and `b` of `vg_poly1305_blocks`: the call of `open`'s. -/
def body (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block toArgs) (Shared.callOpen x b)

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
