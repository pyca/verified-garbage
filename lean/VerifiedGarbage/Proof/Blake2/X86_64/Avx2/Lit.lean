module

public import VerifiedGarbage.Impl.Blake2.X86_64.Avx2
public import VerifiedGarbage.Impl.Blake2.X86_64.Stream
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blake2.X86_64.Avx2
meta import VerifiedGarbage.Impl.Blake2.X86_64.Stream
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# BLAKE2b on x86-64 with AVX2: the code as literals

The compression function, and the streaming `update` and `finalize` calling
it (`avx2`, the callee they are emitted with), as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx2

/-- The compression function, as the streaming functions call it. -/
def avx2 : Impl.Blake2.X86_64.Stream.Callee :=
  ⟨"vg_blake2b_compress" ++ "_avx2", Impl.Blake2.X86_64.Avx2.compress⟩

materialize_code compressY := Impl.Blake2.X86_64.Avx2.compress
materialize_code updateY := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b avx2
materialize_code finalizeY := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b avx2

end VG.Proof.Blake2.X86_64.Avx2
