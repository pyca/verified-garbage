module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Ifma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# The IFMA Miller–Rabin round: the code as a literal

Each layout's round is unrolled, so the kernel would build its instructions
again in every check that evaluates it (its `ctlOk` and stack checks, and
its constant-time check): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

materialize_code ifma1024 := Impl.MillerRabin.X86_64.Ifma.ifma Impl.Rsa.X86_64.PubIfma.pay1024
materialize_code ifma1536 := Impl.MillerRabin.X86_64.Ifma.ifma Impl.Rsa.X86_64.PubIfma.pay1536
materialize_code ifma2048 := Impl.MillerRabin.X86_64.Ifma.ifma Impl.Rsa.X86_64.PubIfma.pay2048
materialize_code ifma3072 := Impl.MillerRabin.X86_64.Ifma.ifma Impl.Rsa.X86_64.PubIfma.pay3072
materialize_code ifma4096 := Impl.MillerRabin.X86_64.Ifma.ifma Impl.Rsa.X86_64.PubIfma.pay4096

-- The frame's bodies, which the constant-time check (`CT.body_t`) evaluates.
materialize_code body1024 := Impl.Bignum.X86_64.seqs (Impl.MillerRabin.X86_64.Ifma.setup Impl.Rsa.X86_64.PubIfma.pay1024 ++
  [Impl.MillerRabin.X86_64.Ifma.vec Impl.Rsa.X86_64.PubIfma.pay1024, .block (Impl.MillerRabin.X86_64.Ifma.finish Impl.Rsa.X86_64.PubIfma.pay1024)])
materialize_code body1536 := Impl.Bignum.X86_64.seqs (Impl.MillerRabin.X86_64.Ifma.setup Impl.Rsa.X86_64.PubIfma.pay1536 ++
  [Impl.MillerRabin.X86_64.Ifma.vec Impl.Rsa.X86_64.PubIfma.pay1536, .block (Impl.MillerRabin.X86_64.Ifma.finish Impl.Rsa.X86_64.PubIfma.pay1536)])
materialize_code body2048 := Impl.Bignum.X86_64.seqs (Impl.MillerRabin.X86_64.Ifma.setup Impl.Rsa.X86_64.PubIfma.pay2048 ++
  [Impl.MillerRabin.X86_64.Ifma.vec Impl.Rsa.X86_64.PubIfma.pay2048, .block (Impl.MillerRabin.X86_64.Ifma.finish Impl.Rsa.X86_64.PubIfma.pay2048)])
materialize_code body3072 := Impl.Bignum.X86_64.seqs (Impl.MillerRabin.X86_64.Ifma.setup Impl.Rsa.X86_64.PubIfma.pay3072 ++
  [Impl.MillerRabin.X86_64.Ifma.vec Impl.Rsa.X86_64.PubIfma.pay3072, .block (Impl.MillerRabin.X86_64.Ifma.finish Impl.Rsa.X86_64.PubIfma.pay3072)])
materialize_code body4096 := Impl.Bignum.X86_64.seqs (Impl.MillerRabin.X86_64.Ifma.setup Impl.Rsa.X86_64.PubIfma.pay4096 ++
  [Impl.MillerRabin.X86_64.Ifma.vec Impl.Rsa.X86_64.PubIfma.pay4096, .block (Impl.MillerRabin.X86_64.Ifma.finish Impl.Rsa.X86_64.PubIfma.pay4096)])

end VG.Proof.MillerRabin.X86_64.Ifma
