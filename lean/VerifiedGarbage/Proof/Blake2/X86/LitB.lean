module

public import VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit
meta import VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit
public import VerifiedGarbage.Impl.Blake2.X86.Stream
meta import VerifiedGarbage.Impl.Blake2.X86.Stream
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# BLAKE2b on x86 (32-bit): the streaming functions as literals

The code of BLAKE2b's streaming functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`). Their calls refer to the compression function's
literal (`Proof/Blake2/X86/CompressB/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.B

materialize_code init := Impl.Blake2.X86.Stream.init Spec.Blake2.b
materialize_code update := Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress
materialize_code finalize :=
  Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress

end VG.Proof.Blake2.X86.B
