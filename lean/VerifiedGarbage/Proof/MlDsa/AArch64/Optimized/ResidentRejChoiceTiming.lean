module

public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideChoice
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideChoice
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha3.AArch64.Call
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad

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
