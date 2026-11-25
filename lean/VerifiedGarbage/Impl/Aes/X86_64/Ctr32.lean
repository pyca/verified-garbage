module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on x86-64

`vg_aes_ctr32(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8, scratch = r9)`,
and its out-of-place form, the internal `vg_aes_ctr32_to`, whose output is at
`r11`: eight blocks at a time (`Sse.lean`), whose counter blocks are made in a
buffer in the scratch space. It uses the first 1376 bytes of the scratch
buffer. No address and no branch depends on anything but the arguments.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64

def ctr32 : Prog isa := Sse.ctr32G false
def ctr32To : Prog isa := Sse.ctr32G true

end VG.Impl.Aes.X86_64
