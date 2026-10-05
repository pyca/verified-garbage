import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Impl.Aes.X86.ExpandKey
import VerifiedGarbage.Impl.Aes.X86.AesNi
import VerifiedGarbage.Impl.Aes.X86.Blocks
import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-! AES implementations that generic x86 callers select by symbol and code. -/
namespace VG.Impl.Aes.X86
open VG.X86
structure Ctr32 where
  name : String
  code : Prog isa
structure ExpandKey where
  name : String
  code : Prog isa
structure Blocks where
  name : String
  code : Prog isa
def Ctr32.scalar : Ctr32 := ⟨"vg_aes_ctr32", ctr32⟩
def Ctr32.aesni : Ctr32 := ⟨"vg_aes_ctr32_aesni", AesNi.ctr32⟩
def ExpandKey.scalar : ExpandKey := ⟨"vg_aes_expand_key", expandKey⟩
def ExpandKey.aesni : ExpandKey := ⟨"vg_aes_expand_key_aesni", AesNi.expandKey⟩
def Blocks.encScalar : Blocks := ⟨"vg_aes_encrypt_blocks", encryptBlocks⟩
def Blocks.decScalar : Blocks := ⟨"vg_aes_decrypt_blocks", decryptBlocks⟩
def Blocks.encAesni : Blocks := ⟨"vg_aes_encrypt_blocks_aesni", AesNi.encryptBlocks⟩
def Blocks.decAesni : Blocks := ⟨"vg_aes_decrypt_blocks_aesni", AesNi.decryptBlocks⟩
end VG.Impl.Aes.X86
