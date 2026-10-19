module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfComplete

/-! # Truncate complete PRF blocks to the exact requested output length -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem PrfInvariant.irprf {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State}
    {R : PrfConfig} {key extra : List Byte}
    (h : PrfInvariant g bs s0 R key extra R.blocks s)
    (blocks : R.blocks = (R.length + 31) / 32) :
    Spec.Rsa.bytesAt s.mem (g.scratch R.dst R.length).base R.length =
      Spec.RsaPkcs1Enc.irprf key (R.label.map (BitVec.ofNat 8)) R.length := by
  change Spec.Rsa.bytesAt s.mem (g.scratch R.dst (32 * R.blocks)).base R.length = _
  rw [VG.Proof.RsaPkcs1Enc.bytesAt_take s.mem (g.scratch R.dst (32 * R.blocks)).base (by rw [blocks]; omega : R.length ≤ 32 * R.blocks), h.prefixBytes, blocks, ← irprf_eq]

end VG.Proof.RsaPkcs1Enc.X86.Dec
