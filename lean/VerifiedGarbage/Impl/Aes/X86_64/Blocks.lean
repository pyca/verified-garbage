module

public import VerifiedGarbage.Impl.Aes.X86_64.Sse

/-!
# AES encryption and decryption of whole blocks, bitsliced, on x86-64

`vg_aes_encrypt_blocks(schedule = rdi, rounds = rsi, data = rdx, n = rcx, scratch = r8)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`):
eight blocks at a time (`Sse.lean`), through a buffer in the scratch space.
No address and no branch depends on anything but the arguments.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64

def encryptBlocks : Prog isa := Sse.blocks Sse.encrypt8
def decryptBlocks : Prog isa := Sse.blocks Sse.decrypt8

end VG.Impl.Aes.X86_64
