module
public import VerifiedGarbage.Proof.Ecdsa.X86.Stages

import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.Stages
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! # ECDSA over P-256 on x86 (32-bit): the constant time of the stages around the comb -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

def signPrepCode : Prog isa := p256Comb.signPrep
def signTailCode : Prog isa := p256Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

theorem signPrep_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp] 5 24))
    signPrepCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

theorem signTail_rel : RelCT isa (VG.X86.Taint.Agree (scratchArgτ 5 true 24))
    signTailCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

end VG.Proof.Ecdsa.X86
