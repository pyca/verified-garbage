module

public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Impl.AesCtr.RISCV64.Final
public import VerifiedGarbage.Impl.AesCfb.RISCV64.Final
public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Impl.AesOfb.RISCV64.Final
public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Impl.CallWipe.RISCV64
public import VerifiedGarbage.Impl.Zeroize.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # AES and its modes on RISC-V: the functions as emitted

Each function, then its cleanup: `Impl.Scrub.RISCV64.scrubAll rb W`, which
zeroes the `W` bytes of stack its frames use and clears the caller-saved
registers but the `rb` bits of the result, or, for the key expansion and
the final partial-block functions of CTR, CFB and OFB, whose code wipes its
own scratch space, `Impl.Scrub.RISCV64.scrubSel rb []`, which clears the
registers and none of the stack (the residue analysis, `RISCV64.rtaint`,
finds no doubleword of it that may differ between two runs). So each
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Aes.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll scrubSel)
open VG.Impl.StackScratch.RISCV64 (withStackScratchWiped)
open VG.Impl.CallWipe.RISCV64 (callWipe)

/-- `vg_aes_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey)

/-- `vg_aes_ecb_encrypt`, as emitted: a call of `vg_aes_encrypt_blocks`,
then of `vg_zeroize` on the 2048 bytes of `scratch`. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 32 (callWipe .a4 2048 "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks
    "vg_zeroize" Impl.Zeroize.RISCV64.zeroize)

/-- `vg_aes_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 32 (callWipe .a4 2048 "vg_aes_decrypt_blocks" Impl.Aes.RISCV64.decryptBlocks
    "vg_zeroize" Impl.Zeroize.RISCV64.zeroize)

/-- `vg_aes_cbc_encrypt`, as emitted: a call of `vg_aes_cbc_encrypt_unwiped`,
then of `vg_zeroize` on the 2176 bytes of `scratch`. -/
def cbcEncrypt : Prog isa :=
  scrubAll 0 32 (callWipe .a5 2176 "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.RISCV64.encrypt
    "vg_zeroize" Impl.Zeroize.RISCV64.zeroize)

/-- `vg_aes_cbc_decrypt`, as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubAll 0 32 (callWipe .a5 2176 "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.RISCV64.decrypt
    "vg_zeroize" Impl.Zeroize.RISCV64.zeroize)

/-- `vg_aes_ctr`, as emitted. -/
def ctr : Prog isa := scrubAll 0 0 Impl.AesCtr.RISCV64.crypt

/-- `vg_aes_ctr_final`, as emitted. -/
def ctrFinal : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 80 .a6 10 Impl.AesCtr.RISCV64.cryptFinal)

/-- `vg_aes_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa := scrubAll 0 0 Impl.AesCfb.RISCV64.encrypt

/-- `vg_aes_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa := scrubAll 0 0 Impl.AesCfb.RISCV64.decrypt

/-- `vg_aes_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.encryptFinal)

/-- `vg_aes_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.decryptFinal)

/-- `vg_aes_cfb8_encrypt`, as emitted. -/
def cfb8Encrypt : Prog isa := scrubAll 0 0 Impl.AesCfb8.RISCV64.encrypt

/-- `vg_aes_cfb8_decrypt`, as emitted. -/
def cfb8Decrypt : Prog isa := scrubAll 0 0 Impl.AesCfb8.RISCV64.decrypt

/-- `vg_aes_ofb`, as emitted. -/
def ofb : Prog isa := scrubAll 0 0 Impl.AesOfb.RISCV64.crypt

/-- `vg_aes_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel 0 [] (withStackScratchWiped 64 .a6 8 Impl.AesOfb.RISCV64.cryptFinal)

/-- `vg_aes_xts_encrypt_unit`, as emitted. -/
def xtsEncryptUnit : Prog isa := scrubAll 0 0 Impl.AesXts.RISCV64Unit.encrypt

/-- `vg_aes_xts_decrypt_unit`, as emitted. -/
def xtsDecryptUnit : Prog isa := scrubAll 0 0 Impl.AesXts.RISCV64Unit.decrypt

end VG.Impl.Aes.RISCV64.Fn
