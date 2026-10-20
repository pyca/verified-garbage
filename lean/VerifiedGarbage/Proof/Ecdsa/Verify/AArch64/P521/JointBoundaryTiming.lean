module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

theorem points_relCT (hc : CfgOk p521) (hC : Law p521.C)
 (hO : PrimeOrder p521.C) (hn : 17≤p521.C.n)
 (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
 (h7 : PubNafWide.PrepChecks P521Joint.KG (p521.sl U))
 (h5 : PubNaf.PrepChecks P521Joint.K (p521.sl V))
 (hwin : WindowChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 {s₀ t₀ : State} (hs : VPre p521 s₀) (ht : VPre p521 t₀) :
 RelCT isa (JointBoundary p521 s₀ t₀) P521Joint.points (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 intro s t ts tt s' t' ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,sp⟩ es et
 let P:=peerPt p521 (s₀.mem (s₀.gpr .x0)=4) (keyX p521 s₀) (keyY p521 s₀)
 have hP : onCurve p521.C P=true:=peerPt_onCurve hc _ _ _
 have peer:=mid_peer_public pub ms mt
 have wins : NafWinPublic p521 (s₀.gpr .x3) P (publicV p521 s₀) s t := by
   refine ⟨⟨ms.scr,⟨gs,ms.fixed⟩,ms.px_lt,ms.py_lt,ms.peer_rep hc hC,mid_publicV ms⟩,
     ⟨mt.scr,⟨gt,mt.fixed⟩,mt.px_lt,mt.py_lt,?_,(mid_publicV mt).trans pub.v.symm⟩,
     sp,peer.1,peer.2⟩
   change Rep _ _ _ _ (peerPt p521 _ _ _)
   rw [pub.peerPoint]
   exact mt.peer_rep hc hC
 have base : s₀.gpr .x3=t₀.gpr .x3 := pub.ptrs.2 .x3 (by decide)
 have tableT : TblPre p521 t₀ (s₀.syms p521.tsym) (s₀.gpr .x3) := by
   rw [base,pub.table]
   exact ht.tbl
 have srcS:=(FixedGenerator.of_pre hc hC hT hs.tbl rfl).unch ms.unch (by decide) ms.rd ms.wr ms.syms
 have symT : t₀.syms "VG_P521_COMB"=s₀.syms p521.tsym := pub.table.symm
 have srcT:=(FixedGenerator.of_pre hc hC hT tableT symT).unch mt.unch (by decide) mt.rd mt.wr mt.syms
 exact jointMul_relCT hc hC hO hn h7 h5 hwin mixed hP _ _ _ _ _ _
   ⟨wins,mid_publicU ms,(mid_publicU mt).trans pub.u.symm,srcS,srcT⟩ es et
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
