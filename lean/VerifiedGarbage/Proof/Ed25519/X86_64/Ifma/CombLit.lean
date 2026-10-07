import VerifiedGarbage.Impl.X25519.X86_64.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit

/-! Checked literals for the comb with AVX512_IFMA, and the functions running it. -/
namespace VG.Proof.Ed25519.X86_64.Zmm
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code combMultiplyLit := (Impl.Ed25519.X86_64.Zmm.combMultiply Impl.X25519.X86_64.adx)
end VG.Proof.Ed25519.X86_64.Zmm

namespace VG
materialize_code scalarBase_ifmaLit := Impl.Ed25519.X86_64.scalarBase_ifma
materialize_code x25519BaseIfmaLit := Impl.X25519.X86_64.Base.x25519BaseIfma
end VG
