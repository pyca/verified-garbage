module

public import VerifiedGarbage.Impl.Blake2.RISCV64.Stream
public import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blake2.RISCV64.Stream
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# Streaming BLAKE2 on RISC-V: the code as literals

The code of the streaming functions of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), with the compression
function's literals (`Proof/Blake2/RISCV64/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream

materialize_code initB := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b
materialize_code updateB := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b
materialize_code updateScratchB := Impl.Blake2.RISCV64.Stream.updateScratch Spec.Blake2.b
materialize_code finalizeB := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b
materialize_code finalizeScratchB := Impl.Blake2.RISCV64.Stream.finalizeScratch Spec.Blake2.b
materialize_code initS := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.s
materialize_code updateS := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.s
materialize_code finalizeS := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.s

end VG.Proof.Blake2.RISCV64.Stream
