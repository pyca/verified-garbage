module

public import VerifiedGarbage.Impl.Sm4Gcm.AArch64
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8

/-!
# SM4-GCM on AArch64: the functions as emitted

Each function is its code in a frame that holds its working space, then its
cleanup (`Impl.Scrub.AArch64.scrubAll`): the registers it writes that the
calling convention does not preserve are cleared, and the stack it uses is
zeroed, so that it returns without secret residue
(`Proof/AesGcm/AArch64/GhashImpls.lean`).

The functions are generic over the implementations they call (`Calls`): of
`vg_ghash`, of `vg_sm4_ctr32` and of `vg_sm4_expand_key`. The last two keep
their working space in frames of their own, below the functions': the cleanup
zeroes those too (`Calls.stack`). It clears the registers AES-GCM's does
(`Impl.AesGcm.AArch64.Fn.own`).

The stream functions are the same code for every implementation of
`vg_ghash`: each calls a function of its own, named for it and the suffix of
the implementation of `vg_sm4_ctr32` (`csfx`), with the address of the
implementation of `vg_ghash` in `d8` (`Impl.Sha3.AArch64.entryD8`), which
calls it by that address (`Code.viaD8At`). Their cleanup clears the high half
of `v8` too (`clearD8`).

`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad` call no cipher: they are
AES-GCM's (`Impl.AesGcm.AArch64.Fn.streamInit`, `streamAad`).
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.AArch64

open VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubAll)
open VG.Impl.StackScratch.AArch64 (withStackScratch withStackArgScratch)
open VG.Impl.AesGcm.AArch64.Fn (own)
open VG.Impl.Sha3.AArch64 (entryD8 clearD8)

/-- What the functions of a variant of SM4-GCM call. -/
structure Calls where
  /-- The implementations of `vg_ghash`, `vg_sm4_ctr32` and
  `vg_sm4_expand_key`. -/
  callees : Callees
  /-- The bytes of stack below the functions' frames that the implementations
  of `vg_sm4_ctr32` and `vg_sm4_expand_key` use. -/
  stack : Nat

namespace Fn

/-- The function named `core`, whose code is `F`, which calls the
implementation of `vg_ghash` of `v` by the address in `d8`, called with that
address there, then the cleanup over `W` bytes of stack and the callees',
for a result of `rb` bits. -/
def viaD8 (v : Calls) (W : Nat) (core : String) (rb : Nat) (F : Prog isa) : Prog isa :=
  scrubAll (v.stack + W) rb clearD8
    (entryD8 v.callees.gh.name core (Impl.Sha3.AArch64.Code.viaD8At v.callees.gh.name F))

/-- `vg_sm4_gcm_init`. -/
def init (v : Calls) : Prog isa :=
  scrubAll (v.stack + 768) 0 own (withStackScratch 768 .x2 (Sm4Gcm.AArch64.init v.callees))

/-- `vg_sm4_gcm_seal`: its working space after a copy of its stack argument. -/
def «seal» (v : Calls) (csfx : String) : Prog isa :=
  viaD8 v 800 ("vg_sm4_gcm_seal_core" ++ csfx) 0 (withStackArgScratch 784 0 (Sm4Gcm.AArch64.«seal» v.callees))

/-- `vg_sm4_gcm_open`, which returns 32 bits. -/
def «open» (v : Calls) : Prog isa :=
  scrubAll (v.stack + 784) 32 own (withStackArgScratch 784 1 (Sm4Gcm.AArch64.«open» v.callees))

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt (v : Calls) (csfx : String) : Prog isa :=
  viaD8 v 784 ("vg_sm4_gcm_stream_encrypt_core" ++ csfx) 0
    (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamEncrypt v.callees))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt (v : Calls) (csfx : String) : Prog isa :=
  viaD8 v 784 ("vg_sm4_gcm_stream_decrypt_core" ++ csfx) 0
    (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamDecrypt v.callees))

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinish (v : Calls) (csfx : String) : Prog isa :=
  viaD8 v 784 ("vg_sm4_gcm_stream_finish_core" ++ csfx) 0
    (withStackScratch 768 .x5 (Sm4Gcm.AArch64.streamFinish v.callees))

/-- `vg_sm4_gcm_stream_verify`, which returns 32 bits. -/
def streamVerify (v : Calls) (csfx : String) : Prog isa :=
  viaD8 v 784 ("vg_sm4_gcm_stream_verify_core" ++ csfx) 32
    (withStackScratch 768 .x6 (Sm4Gcm.AArch64.streamVerify v.callees))

end Fn

end VG.Impl.Sm4Gcm.AArch64
