module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedTable
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

theorem points_relCT (hc : CfgOk p384) (hC : Law p384.C)
 (hO : PrimeOrder p384.C) (hn : 17≤p384.C.n)
 (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V))
 (hwin : WindowChecks P384Joint.K)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 {s₀ t₀ : State} (hs : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s₀)
 (ht : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords t₀) :
 RelCT isa (JointBoundaryT p384 "VG_P384_GTAB" s₀ t₀) P384Joint.points (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 intro s t ts tt s' t' ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,sp⟩ es et
 let P:=peerPt p384 (s₀.mem (s₀.gpr .x0)=4) (keyX p384 s₀) (keyY p384 s₀)
 have hP : onCurve p384.C P=true:=peerPt_onCurve hc _ _ _
 have peer:=mid_peer_public pub ms mt
 have wins : NafWinPublic p384 (s₀.gpr .x3) P (publicV p384 s₀) s t := by
   refine ⟨⟨ms.scr,⟨gs,ms.fixed⟩,ms.px_lt,ms.py_lt,ms.peer_rep hc hC,mid_publicV ms⟩,
     ⟨mt.scr,⟨gt,mt.fixed⟩,mt.px_lt,mt.py_lt,?_,(mid_publicV mt).trans pub.v.symm⟩,
     sp,peer.1,peer.2⟩
   change Rep _ _ _ _ (peerPt p384 _ _ _)
   rw [pub.peerPoint]
   exact mt.peer_rep hc hC
 have base : s₀.gpr .x3=t₀.gpr .x3 := pub.ptrs.2 .x3 (by decide)
 have tableT : TblPreW P384Joint.p384v.combWords t₀ (s₀.syms "VG_P384_GTAB") (s₀.gpr .x3) := by
   rw [base,pub.table]
   exact ht.tbl
 have srcS:=(FixedGenerator.of_pre hc hC hT hs.tbl rfl).unch ms.unch (by decide) ms.rd ms.wr ms.syms
 have symT : t₀.syms "VG_P384_GTAB"=s₀.syms "VG_P384_GTAB" := pub.table.symm
 have srcT:=(FixedGenerator.of_pre hc hC hT tableT symT).unch mt.unch (by decide) mt.rd mt.wr mt.syms
 exact jointMul_relCT hc hC hO hn h9 h5 hwin hD hct mixed hP _ _ _ _ _ _
   ⟨wins,mid_publicU ms,(mid_publicU mt).trans pub.u.symm,srcS,srcT⟩ es et
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
