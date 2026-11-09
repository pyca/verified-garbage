module

import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves

/-! RFC 6979 scratch sizes are part of the emitted signature and contract:
8 KiB for every curve, brainpoolP512r1 included, whose wrappers keep its
64-byte reduced digest in their stack frames. -/

open VG VG.Spec.Ecdsa.Rfc6979

example : Curves.brainpoolp384r1.signSig.params =
    [("out", .array true .u8 96), ("d", .array false .u8 48),
      ("digest", .slice false .u8 "digest_len"), ("scratch", .array true .u64 1024),
      ("hmac", Spec.HmacTable.param)] := rfl

example : Curves.brainpoolp512r1SignApi.sig.params =
    [("out", .array true .u8 128), ("d", .array false .u8 64),
      ("digest", .slice false .u8 "digest_len"), ("scratch", .array true .u64 1024),
      ("hmac", Spec.HmacTable.param)] := rfl

example : Curves.brainpoolp512r1.scratchWords = Spec.Ecdsa.scratchWords := rfl
