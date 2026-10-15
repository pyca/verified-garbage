module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sha3.X86_64.Stream
meta import VerifiedGarbage.Impl.Sha3.X86_64.Stream
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Hint
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Hint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-DSA on x86-64: the functions its top-level functions call, as literals

The Keccak functions and the functions of ML-DSA that do not depend on the
polynomial arithmetic, as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), so that the literals of the functions calling
them refer to them, and the kernel checks each once
(`Proof/MlDsa/X86_64/Sign/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha3.X86_64.permute
materialize_code Impl.Sha3.X86_64.Stream.absorb
materialize_code Impl.Sha3.X86_64.Stream.pad
materialize_code Impl.Sha3.X86_64.Stream.squeeze
materialize_code Impl.MlDsa.X86_64.Sample.sampleInBall
materialize_code Impl.MlDsa.X86_64.Pack.bitUnpack
materialize_code Impl.MlDsa.X86_64.Pack.simpleBitPack
materialize_code Impl.MlDsa.X86_64.Pack.bitPack
materialize_code Impl.MlDsa.X86_64.Pack.hintBitPack

end VG
