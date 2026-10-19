module
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.MlKem.Arith

/-! # Clear the suffix of a failed continued matrix sample -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem zeroExtra_ok {w16 : Bool} (s : State) {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {L : List Zq} {aP : Addr} (hl : L.length≤256)
    (hc : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (hcp : checkpointW w16 (s.gpr .x19+BitVec.ofNat 64 slot) aP L s.mem)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8)
    (hw : ∀i<256,InRegions s.wr (cAddr w16 aP i) 4) :
    WP isa (Impl.MlKem.AArch64.Paired.zeroExtra slot w16) s fun u =>
      Keep [.x3,.x4,.x13] s u ∧ Frame [polyRegion aP] s.mem u.mem ∧
      CoeffsUpToW w16 u.mem aP L.length (Sample.cvW w16 L) (fun _ => 0) ∧ ReducedW (cw w16) u.mem aP := by
  refine WP.seq (WP.mono (load_checkpoint s ho ha h0 h1) fun a ⟨ha,_,a3,a4⟩ => ?_)
  refine WP.mono (Rej8.zeroSuffix_prefix (by rw [ha.wr]; exact hw) hl
    (by rw [ha.mem]; exact hc) (a3.trans hcp.1) (by
      rw [a4,show s.gpr .x19+BitVec.ofNat 64 (slot+8)=s.gpr .x19+BitVec.ofNat 64 slot+8 by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl]
      exact hcp.2)) fun u ⟨hu,hf,hc⟩ => ?_
  exact ⟨(ha.keep.trans hu).mono (by decide),by rw [←ha.mem]; exact hf,hc,Sample.reduced_of_coeffs hc⟩

end VG.Proof.MlKem.AArch64.Paired
