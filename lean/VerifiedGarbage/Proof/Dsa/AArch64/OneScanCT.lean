module

public import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Fixed-trace subgroup result checks -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem oneScan_ct : RelCT isa (Two GoodW) Checks.oneScan (fun _ _ => True) := by
  unfold Checks.oneScan seqs
  exact RelCT.seq scanHead_ct (two_taint [.x12, .x16] pins_scanAddresses (by taint_decide))

theorem oneMask_ct : RelCT isa (Two LoadedCheck)
    (.seq Checks.oneScan (.block (Checks.zeroMask .x15))) (Two fun (p : BPub) s => LinkedPre p.x s) := by
  refine RelCT.seq (two_post (Ψ := fun (p : BPub) s => LinkedPre p.x s)
    (two_map (fun p : BPub => p.x.ws) (fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) oneScan_ct) ?_) ?_
  · intro p s ⟨minv, hc, hw, hw'⟩
    exact WP.mono (oneScan_ok hc.good (Nat.le_refl _) hw hw')
      fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩
  refine two_piece (Ψ := fun (p : BPub) s => LinkedPre p.x s) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_
  intro p s ⟨minv, hc⟩
  exact WP.mono (zeroMask_ok .x15 false) fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩

end VG.Proof.Dsa.AArch64
