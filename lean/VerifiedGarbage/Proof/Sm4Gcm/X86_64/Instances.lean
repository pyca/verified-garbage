module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame

/-!
# SM4-GCM on x86-64: the instances

Untrusted: everything here is checked by Lean. What the SM4-GCM functions
generic over `vg_ghash` (`Generic/Ghash/X86_64/Sm4Gcm.lean`) are built from:
for each implementation of `vg_ghash` (a variant of `Ghash`, named by AES-GCM's
`GhashName`), AES-GCM's callees with it (`gcmOf`), the proofs of the SM4-GCM
functions (and of `stream_init` and `stream_aad`, AES-GCM's code) taking
them. Of those callees the SM4-GCM functions call only `vg_ghash`: the AES
ones are the baseline's, which no SM4-GCM function calls.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG.Proof.AesGcm.X86_64 (GcmImpl GhashName)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- AES-GCM's callees with the implementation `n` of `vg_ghash`. -/
def gcmOf (n : GhashName) : GcmImpl where
  ctr := Ctr32Impl.scalar
  key := Proof.AesGcm.X86_64.KeyImpl.scalar
  gh := n.impl

end VG.Proof.Sm4Gcm.X86_64
