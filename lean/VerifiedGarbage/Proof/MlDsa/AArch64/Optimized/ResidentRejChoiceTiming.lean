module

public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def choicePublic (vs : List VReg) : VectorTaint.T :=
  (Taint.ofRegs [.x3,.x4,.x6,.x9],RegSet.ofList vs)

theorem fourChoice_ct : ConstantTime isa (fun _ => True)
    (VectorTaint.Agree (choicePublic [.v1]))
    (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) :=
  VG.Taint.constantTime (A := VectorTaint.taint) (choicePublic [.v1])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem wideChoice_ct : ConstantTime isa (fun _ => True)
    (VectorTaint.Agree (choicePublic [.v16,.v17,.v18,.v19]))
    (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)) :=
  VG.Taint.constantTime (A := VectorTaint.taint) (choicePublic [.v16,.v17,.v18,.v19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem vectorTry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block vectorTry) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem wideTry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block wideTry) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
