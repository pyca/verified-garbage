import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
import VerifiedGarbage.Impl.Aes.X86_64.AesNi
import VerifiedGarbage.Impl.Aes.X86_64.Vaes
import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
import VerifiedGarbage.Impl.Aes.X86_64.Blocks
import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks
import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

/-!
# The implementations of `vg_aes_ctr32` on x86-64

A function that calls `vg_aes_ctr32` (AES-CMAC's) takes the implementation it
calls, a `Ctr32`, and is emitted once for each (`Generic/AesCtr32/X86_64/`).
One that also expands the key (streaming AES-CMAC's `init`) calls the
implementation of `vg_aes_expand_key_scratch` that goes with it, an `ExpandKey`.
A function that encrypts or decrypts whole blocks (AES-OCB's) calls an
implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, a
pair of `Blocks`.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- An implementation of `vg_aes_ctr32` to call: its symbol and its code. -/
structure Ctr32 where
  name : String
  code : Prog isa

def Ctr32.scalar : Ctr32 := ⟨"vg_aes_ctr32", ctr32⟩
def Ctr32.aesni : Ctr32 := ⟨"vg_aes_ctr32_aesni", AesNi.ctr32⟩
def Ctr32.vaes : Ctr32 := ⟨"vg_aes_ctr32_vaes", Vaes.ctr32⟩

/-- An implementation of `vg_aes_expand_key_scratch` to call: its symbol and its code. -/
structure ExpandKey where
  name : String
  code : Prog isa

def ExpandKey.scalar : ExpandKey := ⟨"vg_aes_expand_key_scratch", expandKey⟩
def ExpandKey.aesni : ExpandKey := ⟨"vg_aes_expand_key_scratch_aesni", AesNi.expandKey⟩

/-- An implementation of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
to call: its symbol and its code. -/
structure Blocks where
  name : String
  code : Prog isa

def Blocks.encScalar : Blocks := ⟨"vg_aes_encrypt_blocks", encryptBlocks⟩
def Blocks.decScalar : Blocks := ⟨"vg_aes_decrypt_blocks", decryptBlocks⟩
def Blocks.encAesni : Blocks := ⟨"vg_aes_encrypt_blocks_aesni", AesNi.encryptBlocks⟩
def Blocks.decAesni : Blocks := ⟨"vg_aes_decrypt_blocks_aesni", AesNi.decryptBlocks⟩
def Blocks.encVaes : Blocks := ⟨"vg_aes_encrypt_blocks_vaes", VaesBlocks.encryptBlocks⟩
def Blocks.decVaes : Blocks := ⟨"vg_aes_decrypt_blocks_vaes", VaesBlocks.decryptBlocks⟩

end VG.Impl.Aes.X86_64
