module

public import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Spec.MlKem
meta import VerifiedGarbage.TCB.X86_64.Target

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
