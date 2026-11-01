module

public import VerifiedGarbage.Impl.AesCbc.RISCV64

/-!
# AES-CFB8: RISC-V implementation

`vg_aes_cfb8_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, len = a4, scratch = a5)`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`): AES-CBC's
encryption's frame (`Impl/AesCbc/RISCV64.lean`, `chainWrapped`: the return
address and `s1` saved in the scratch buffer) around a call of the CFB8
chain (`Impl.Aes.RISCV64.cfb8Chain`), which bitslices the round keys once
for all the bytes and, for each byte, enciphers the input block, XORs its
first byte into the data byte, and shifts the input block left by a byte,
with the ciphertext byte shifted in.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (chainWrapped)

/-- Each byte, by the CFB8 chain (`Impl.Aes.RISCV64.cfb8Chain`), which
bitslices the round keys once for all the bytes. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfb8EncChainCall

def decrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfb8DecChainCall

end VG.Impl.AesCfb8.RISCV64
