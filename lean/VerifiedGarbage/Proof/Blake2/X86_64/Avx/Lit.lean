module

public import VerifiedGarbage.Impl.Blake2.X86_64.Avx
public import VerifiedGarbage.Impl.Blake2.X86_64.Stream
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blake2.X86_64.Avx
meta import VerifiedGarbage.Impl.Blake2.X86_64.Stream
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# BLAKE2s on x86-64 with AVX: the code as literals

The compression function, and the streaming `update` and `finalize` calling
it (`avx`, the callee they are emitted with), as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx

/-- The compression function, as the streaming functions call it. -/
def avx : Impl.Blake2.X86_64.Stream.Callee :=
  ⟨"vg_blake2s_compress" ++ "_avx", Impl.Blake2.X86_64.Avx.compress⟩

materialize_code compressX := Impl.Blake2.X86_64.Avx.compress
materialize_code updateX := Impl.Blake2.X86_64.Stream.update Spec.Blake2.s avx
materialize_code finalizeX := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s avx

end VG.Proof.Blake2.X86_64.Avx
