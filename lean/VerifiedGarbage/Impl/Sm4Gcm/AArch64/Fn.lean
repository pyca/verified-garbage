module

public import VerifiedGarbage.Impl.Sm4Gcm.AArch64
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# SM4-GCM on AArch64: the functions as emitted

Each function is its code in a frame that holds its working space, then its
cleanup (`Impl.Residue.AArch64.scrubAll`): the registers it writes that the
calling convention does not preserve are cleared, and the stack it uses is
zeroed, so that it returns without secret residue
(`Proof/AesGcm/AArch64/GhashImpls.lean`).

The functions are generic over the implementations they call (`Calls`): of
`vg_ghash`, of `vg_sm4_ctr32` and of `vg_sm4_expand_key`. The last two keep
their working space in frames of their own, below the functions': the cleanup
zeroes those too (`Calls.stack`). It clears the registers AES-GCM's does
(`Impl.AesGcm.AArch64.Fn.own`).

`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad` call no cipher: they are
AES-GCM's (`Impl.AesGcm.AArch64.Fn.streamInit`, `streamAad`).
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.AArch64

open VG.AArch64
open VG.Impl.Residue.AArch64 (scrubAll)
open VG.Impl.StackScratch.AArch64 (withStackScratch withStackArgScratch)
open VG.Impl.AesGcm.AArch64.Fn (own)

/-- What the functions of a variant of SM4-GCM call. -/
structure Calls where
  /-- The implementations of `vg_ghash`, `vg_sm4_ctr32` and
  `vg_sm4_expand_key`. -/
  callees : Callees
  /-- The bytes of stack below the functions' frames that the implementations
  of `vg_sm4_ctr32` and `vg_sm4_expand_key` use. -/
  stack : Nat

namespace Fn

/-- `vg_sm4_gcm_init`. -/
def init (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 0 own (withStackScratch 768 .x2 (Sm4Gcm.AArch64.init v.callees))

/-- `vg_sm4_gcm_seal`: its working space after a copy of its stack argument. -/
def «seal» (v : Calls) : Prog isa :=
  scrubAll (v.stack + 784) 0 own (withStackArgScratch 784 0 (Sm4Gcm.AArch64.«seal» v.callees))

/-- `vg_sm4_gcm_open`, which returns 32 bits. -/
def «open» (v : Calls) : Prog isa :=
  scrubAll (v.stack + 784) 32 own (withStackArgScratch 784 1 (Sm4Gcm.AArch64.«open» v.callees))

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 0 own (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamEncrypt v.callees))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 0 own (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamDecrypt v.callees))

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinish (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 0 own (withStackScratch 768 .x5 (Sm4Gcm.AArch64.streamFinish v.callees))

/-- `vg_sm4_gcm_stream_verify`, which returns 32 bits. -/
def streamVerify (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 32 own (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamVerify v.callees))

end Fn

end VG.Impl.Sm4Gcm.AArch64
