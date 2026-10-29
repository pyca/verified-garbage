module

public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingShapeCT

import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedBody
import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedComputeCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Execution
/-! # The public schedule after independent verifying-workspace initialization -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/PrevalidatedBodyCT.lean`, which only this module imported.
section

/-! # Constant time through validation, computation and the ABI return -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedComputeReturn_ok (M : Mont) {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    WP isa (Prevalidated.compute M.mm) s (fun t => t.gpr .x0 = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (prevalidatedCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.rLength ho.sLength
    ho.digestBound hm) fun _ h => h.1.parent.x0

theorem prevalidatedBody_ct (M : Mont) : RelCT isa (Two VerifyingBodyPre) (prevalidatedBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .x0 = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedComputeReturn_ok M h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Prevalidated.compute M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  exact (prevalidatedBody_ct M).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64
