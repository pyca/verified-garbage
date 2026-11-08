module

public import VerifiedGarbage.Impl.Aes.X86.ExpandKey
public import VerifiedGarbage.Impl.Aes.X86.Blocks
public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-! AES implementations that generic x86 callers select by symbol and code. -/

@[expose] public section

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
/-- `vg_aes_ctr32` out of place: from `src` (argument 3) to `dst` (argument 6). -/
def Ctr32.scalarTo : Ctr32 := ⟨"vg_aes_ctr32_to", ctr32To⟩
def Ctr32.aesniTo : Ctr32 := ⟨"vg_aes_ctr32_to_aesni", AesNi.ctr32To⟩
def ExpandKey.scalar : ExpandKey := ⟨"vg_aes_expand_key_scratch", expandKey⟩
def ExpandKey.aesni : ExpandKey := ⟨"vg_aes_expand_key_scratch_aesni", AesNi.expandKey⟩
def Blocks.encScalar : Blocks := ⟨"vg_aes_encrypt_blocks", encryptBlocks⟩
def Blocks.decScalar : Blocks := ⟨"vg_aes_decrypt_blocks", decryptBlocks⟩
def Blocks.encAesni : Blocks := ⟨"vg_aes_encrypt_blocks_aesni", AesNi.encryptBlocks⟩
def Blocks.decAesni : Blocks := ⟨"vg_aes_decrypt_blocks_aesni", AesNi.decryptBlocks⟩
end VG.Impl.Aes.X86
