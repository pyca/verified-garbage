module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums


/-! # Save a resumed sampler's output cursor and success flag -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG.Impl.MlKem.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure SavedPostW (w16 : Bool) (L : List Zq) (aP p : Addr) (s u : State) : Prop where
  keep : Keep [] s u
  frame : Frame [⟨p,16⟩] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP L
  checkpoint : checkpointW w16 p aP L u.mem
  x3 : u.gpr .x3=cAddr w16 aP L.length
  x4 : (u.gpr .x4).toNat=256-L.length

theorem store_ok {w16 : Bool} (s : State) {r : Reg} {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {L : List Zq} {aP : Addr} (hl : L.length≤256)
    (hc : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (h0 : InRegions s.wr (s.gpr r+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr r+BitVec.ofNat 64 (slot+8)) 8)
    (hd : (polyRegion aP).Disjoint ⟨s.gpr r+BitVec.ofNat 64 slot,16⟩) :
    WP isa (.block [.str .x .x3 r slot,.str .x .x4 r (slot+8)]) s
      (SavedPostW w16 L aP (s.gpr r+BitVec.ofNat 64 slot) s) := by
  refine WP.mono (store_checkpoint s ho ha h0 h1) fun u ⟨hu,_,fr,p3,p4⟩ => ?_
  refine ⟨hu,fr,?_,?_,by rw [hu.get .x3,h3],by rw [hu.get .x4,h4]⟩
  · intro i hi
    rw [coeffAtW_frame fr (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by omega)]
    exact hc i hi
  · refine ⟨by rw [p3,h3],?_⟩
    have haddr : s.gpr r+BitVec.ofNat 64 slot+8=s.gpr r+BitVec.ofNat 64 (slot+8) := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    rw [haddr,p4,h4]

end VG.Proof.MlKem.AArch64.Paired
