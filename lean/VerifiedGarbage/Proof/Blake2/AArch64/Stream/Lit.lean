module

public import VerifiedGarbage.Proof.Blake2.AArch64.Lit
public import VerifiedGarbage.Impl.Blake2.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Blake2.AArch64.Lit
meta import VerifiedGarbage.Impl.Blake2.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Streaming BLAKE2 on AArch64: the code as literals

`init`, `update` and `finalize` of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), whose calls refer to the
literals of the compression functions (`Proof/Blake2/AArch64/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Stream

materialize_code initB := Impl.Blake2.AArch64.Stream.init Spec.Blake2.b
materialize_code updateB := Impl.Blake2.AArch64.Stream.update Spec.Blake2.b
materialize_code finalizeB := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b
materialize_code initS := Impl.Blake2.AArch64.Stream.init Spec.Blake2.s
materialize_code updateS := Impl.Blake2.AArch64.Stream.update Spec.Blake2.s
materialize_code finalizeS := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.s

end VG.Proof.Blake2.AArch64.Stream
