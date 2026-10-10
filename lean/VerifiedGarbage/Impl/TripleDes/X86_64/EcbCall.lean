import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx512
import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES ECB on x86-64, calling one copy of the SSE2 code

`vg_triple_des_ecb_{en,de}crypt_core(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`
is the SSE2 code (`BitsliceSse.ecb`: batches of 128 blocks, then the
64-block code), with its working space as an argument. Every ECB function
calls it for the blocks it leaves (`inner`), in place of a copy of that code:
the baseline function for all of them, the AVX2 one after its batches of
256 blocks, and the AVX-512 one after its batches of 512 and then of 256.
The frame around each (`withStackScratchWiped`) allocates the working space,
whose pointer stays in `rcx` for the call.
-/

namespace VG.Impl.TripleDes.X86_64.EcbCall

open VG.X86_64
open VG.Spec.TripleDes (Direction)

/-- The core's code. -/
def core : Direction → Prog isa
  | .encrypt => BitsliceSse.encrypt
  | .decrypt => BitsliceSse.decrypt

/-- The core's name. -/
def coreName : Direction → String
  | .encrypt => Spec.TripleDes.ecbEncryptCoreApi.name
  | .decrypt => Spec.TripleDes.ecbDecryptCoreApi.name

/-- A call of the core. -/
def coreCall (d : Direction) : Prog isa := .call (coreName d) (core d)

/-- The baseline ECB functions' code in their frame. -/
def sse (d : Direction) : Prog isa := coreCall d

/-- The AVX2 ones'. -/
def avx2 (d : Direction) : Prog isa := .seq (BitsliceAvx2.wide d) (coreCall d)

/-- The AVX-512 ones'. -/
def avx512 (d : Direction) : Prog isa := .seq (BitsliceAvx512.wide d) (avx2 d)

def sseEncrypt : Prog isa := sse .encrypt
def sseDecrypt : Prog isa := sse .decrypt
def avx2Encrypt : Prog isa := avx2 .encrypt
def avx2Decrypt : Prog isa := avx2 .decrypt
def avx512Encrypt : Prog isa := avx512 .encrypt
def avx512Decrypt : Prog isa := avx512 .decrypt

end VG.Impl.TripleDes.X86_64.EcbCall
