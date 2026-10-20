module

public import VerifiedGarbage.Impl.Blake2.X86.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blake2.X86.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# BLAKE2s on x86 (32-bit): the code as literals

The code of BLAKE2s's compression function and of its streaming functions as
literals (`materialize_code`, `Proof/Framework/Lit.lean`). The streaming
functions' calls refer to the compression function's literal.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.S

materialize_code compress := Impl.Blake2.X86.CompressS.compress
materialize_code init := Impl.Blake2.X86.Stream.init Spec.Blake2.s
materialize_code update := Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress
materialize_code finalize :=
  Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress

end VG.Proof.Blake2.X86.S
