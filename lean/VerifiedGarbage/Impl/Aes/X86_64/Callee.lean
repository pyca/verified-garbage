module

public import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Aes.X86_64.Blocks
public import VerifiedGarbage.Impl.Aes.X86_64.Sse
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

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

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- An implementation of `vg_aes_ctr32` to call: its symbol and its code,
and how far into their scratch buffer the functions that keep it for one
(AES-CMAC's, which call it on one block at a time) give it its working space
(`scrOff`): 0, or for an implementation that uses less than the 2048 bytes
set aside for it, enough that the bytes it leaves unused are the first of
their buffer, which a caller of those functions then need not set aside. -/
structure Ctr32 where
  name : String
  code : Prog isa
  scrOff : Nat := 0

/-- The bitsliced implementation uses the first 1480 bytes of its scratch
buffer: 512 bytes into a buffer of 2048, it leaves the first 512 unused. -/
def Ctr32.scalar : Ctr32 := { name := "vg_aes_ctr32", code := ctr32, scrOff := 512 }
def Ctr32.aesni : Ctr32 := { name := "vg_aes_ctr32_aesni", code := AesNi.ctr32 }
def Ctr32.vaes : Ctr32 := { name := "vg_aes_ctr32_vaes", code := Vaes.ctr32 }

/-- `vg_aes_ctr32_aesni` out of place (`AesNi.ctr32To`). -/
def Ctr32.aesniTo : Ctr32 := { name := "vg_aes_ctr32_to_aesni", code := AesNi.ctr32To }

/-- `vg_aes_ctr32_vaes` out of place (`Vaes.ctr32To`). -/
def Ctr32.vaesTo : Ctr32 := { name := "vg_aes_ctr32_to_vaes", code := Vaes.ctr32To }

/-- `vg_aes_ctr32` out of place (`ctr32To`). -/
def Ctr32.scalarTo : Ctr32 := { name := "vg_aes_ctr32_to", code := ctr32To }

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

/-- How much working space an implementation of the AES functions needs,
which picks the code of the functions that call it and their frames: none
(`free`), 1480 bytes from 512 bytes into a scratch buffer (`small`), or all
2048 (`full`). -/
inductive Space
  | free
  | small
  | full
  deriving DecidableEq, Repr

end VG.Impl.Aes.X86_64
