import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Blake2.X86_64.Avx2
import VerifiedGarbage.Impl.Blake2.X86_64.Stream
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2b on x86-64 with AVX2: the code as literals

The compression function, and the streaming `update` and `finalize` calling
it (`avx2`, the callee they are emitted with), as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG.Proof.Blake2.X86_64.Avx2

/-- The compression function, as the streaming functions call it. -/
def avx2 : Impl.Blake2.X86_64.Stream.Callee :=
  ⟨Spec.Blake2.compressBApi.name ++ "_avx2", Impl.Blake2.X86_64.Avx2.compress⟩

materialize_code compressY := Impl.Blake2.X86_64.Avx2.compress
materialize_code updateY := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b avx2
materialize_code finalizeY := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b avx2

end VG.Proof.Blake2.X86_64.Avx2
