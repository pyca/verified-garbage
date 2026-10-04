import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Blake2.X86_64.Avx
import VerifiedGarbage.Impl.Blake2.X86_64.Stream
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2s on x86-64 with AVX: the code as literals

The compression function, and the streaming `update` and `finalize` calling
it (`avx`, the callee they are emitted with), as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG.Proof.Blake2.X86_64.Avx

/-- The compression function, as the streaming functions call it. -/
def avx : Impl.Blake2.X86_64.Stream.Callee :=
  ⟨Spec.Blake2.compressSApi.name ++ "_avx", Impl.Blake2.X86_64.Avx.compress⟩

materialize_code compressX := Impl.Blake2.X86_64.Avx.compress
materialize_code updateX := Impl.Blake2.X86_64.Stream.update Spec.Blake2.s avx
materialize_code finalizeX := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s avx

end VG.Proof.Blake2.X86_64.Avx
