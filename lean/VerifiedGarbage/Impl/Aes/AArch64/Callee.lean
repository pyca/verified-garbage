import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
import VerifiedGarbage.Impl.Aes.AArch64.Aese
import VerifiedGarbage.Impl.Aes.AArch64.Blocks
import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks

/-!
# The implementations of `vg_aes_ctr32` on AArch64

A function that calls `vg_aes_ctr32` (AES-CMAC's) takes the implementation it
calls, a `Ctr32`, and is emitted once for each (`Generic/AesCtr32/AArch64/`).
One that also expands the key (streaming AES-CMAC's `init`) calls the
implementation of `vg_aes_expand_key_scratch` that goes with it, an `ExpandKey`.
A function that encrypts or decrypts whole blocks (AES-OCB's) calls an
implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, a
pair of `Blocks`.
-/

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_ctr32` to call: its symbol and its code. -/
structure Ctr32 where
  name : String
  code : Prog isa

def Ctr32.scalar : Ctr32 := ⟨"vg_aes_ctr32", ctr32⟩
def Ctr32.aese : Ctr32 := ⟨"vg_aes_ctr32_aes", Aese.ctr32⟩

/-- An implementation of `vg_aes_expand_key_scratch` to call: its symbol and its code. -/
structure ExpandKey where
  name : String
  code : Prog isa

def ExpandKey.scalar : ExpandKey := ⟨"vg_aes_expand_key_scratch", expandKey⟩
def ExpandKey.aese : ExpandKey := ⟨"vg_aes_expand_key_scratch_aes", Aese.expandKey⟩

/-- An implementation of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
to call: its symbol and its code. -/
structure Blocks where
  name : String
  code : Prog isa

def Blocks.encScalar : Blocks := ⟨"vg_aes_encrypt_blocks", encryptBlocks⟩
def Blocks.decScalar : Blocks := ⟨"vg_aes_decrypt_blocks", decryptBlocks⟩
def Blocks.encAese : Blocks := ⟨"vg_aes_encrypt_blocks_aes", Aese.encryptBlocks⟩
def Blocks.decAese : Blocks := ⟨"vg_aes_decrypt_blocks_aes", Aese.decryptBlocks⟩

end VG.Impl.Aes.AArch64
