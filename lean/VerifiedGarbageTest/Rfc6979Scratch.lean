module

import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512

/-! RFC 6979 scratch sizes are part of the emitted signature and contract:
8 KiB for every curve, brainpoolP512r1 included, whose wrappers keep its
64-byte reduced digest in their stack frames. -/

open VG VG.Spec.Ecdsa.Rfc6979

example : BrainpoolP384r1Sha384.inst.signSig.params =
    [("out", .array true .u8 96), ("d", .array false .u8 48),
      ("digest", .array false .u8 48), ("scratch", .array true .u64 1024)] := rfl

example : BrainpoolP512r1Sha512.signApi.sig.params =
    [("out", .array true .u8 128), ("d", .array false .u8 64),
      ("digest", .array false .u8 64), ("scratch", .array true .u64 1024)] := rfl

example : BrainpoolP512r1Sha512.inst.scratchWords = Spec.Ecdsa.scratchWords := rfl
