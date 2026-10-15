module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
public import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Avx2
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Avx2
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-DSA on x86-64: the AVX2 arithmetic as literals

The code of the functions of `Backend.avx2Combined`, built by functions
(unrolled layers, `yconst`, …), as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), for the checks that evaluate it
(`ArithImpl.avx2`).
-/

@[expose] public section

namespace VG

open Impl.MlDsa.X86_64

materialize_code Arith.lazyNtt
materialize_code Arith.montNttInvAvx2
materialize_code Arith.montMulAvx2
materialize_code Arith.montMulAddAvx2
materialize_code Arith.addAvx2
materialize_code Arith.subAvx2
materialize_code Round.highBitsAvx2
materialize_code Round.lowBitsAvx2
materialize_code Round.normLtAvx2
materialize_code Round.makeHintAvx2
materialize_code Round.useHintAvx2
materialize_code Sample.Rej5.rejNTT4Avx2
materialize_code Sample.Mask4.expandMask4Avx2

end VG
