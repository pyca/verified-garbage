import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512

/-! RFC 6979 scratch sizes are part of the emitted signature and contract.
The existing default stays at 8 KiB; brainpoolP512r1 reserves another
64 bytes to retain its reduced digest across calls of the signing core. -/

open VG VG.Spec.Ecdsa.Rfc6979

example : BrainpoolP384r1Sha384.inst.signSig.params =
    [("out", .array true .u8 96), ("d", .array false .u8 48),
      ("digest", .array false .u8 48), ("scratch", .array true .u64 1024)] := rfl

example : BrainpoolP512r1Sha512.signApi.sig.params =
    [("out", .array true .u8 128), ("d", .array false .u8 64),
      ("digest", .array false .u8 64), ("scratch", .array true .u64 1032)] := rfl

example : 8 * BrainpoolP512r1Sha512.inst.scratchWords =
    8 * Spec.Ecdsa.scratchWords + 64 := rfl
