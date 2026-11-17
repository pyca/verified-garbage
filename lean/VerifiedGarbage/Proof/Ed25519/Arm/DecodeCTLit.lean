module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
public import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
meta import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code recoverCandidatePlain := recoverCandidate false
materialize_code recoverCandidateUmaal := recoverCandidate true
materialize_code pointDecodeLoad
materialize_code recoverSuccessPlain := recoverSuccess false
materialize_code recoverSuccessUmaal := recoverSuccess true
materialize_code equal116CT := fieldEqual 11 6
materialize_code equal1112CT := fieldEqual 11 12
materialize_code equal89CT := fieldEqual 8 9
materialize_code equal1011CT := fieldEqual 10 11
materialize_code equalOpsCT := fieldCode false pointEqualOps
materialize_code equalOpsUmaalCT := fieldCode true pointEqualOps
materialize_code zero0CT := fieldZero 0
materialize_code parityCT := (.block (freeze 0 ++ recoverParity) : Prog isa)
materialize_code negateCT := fieldCode false [.const 5 0, .sub 0 5 0]
materialize_code rootAdjustCT := fieldCode false [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]
materialize_code rootAdjustUmaalCT := fieldCode true [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]
end VG.Proof.Ed25519.Arm
