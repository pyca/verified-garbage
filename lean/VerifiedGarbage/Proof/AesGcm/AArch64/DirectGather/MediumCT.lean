module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumKeys
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumBody
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLoopEnd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLayout
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentCT
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! Constant-time composition of the bounded two-batch gather. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64.Gather

theorem prefix_rel {a b : State} (la : BoundedLay a) (lb : BoundedLay b)
    (an : L a ≤ 224) (bn : L b ≤ 224) (pub : gatherPub a b) :
    RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b))
      (.seq (.block Medium.setup) (.seq (.block Medium.zero) Medium.aad)) TT := by
  obtain ⟨_,_,_,_,q4,q5,_,_,sp,_,_,len,_,_⟩ := pub
  have w : base a = base b := by simp only [base,sp]
  refine rel_seq (rel_taint [] w (by agree_tac []) ⟨_,by taint_decide⟩)
    (entered la an) (entered lb bn) ?_
  intro x y ⟨p,x4⟩ ⟨q,y4⟩
  exact rel_taint [.x4,.x19,.x24,.x25] (p.sp.trans (w.trans q.sp.symm))
    (by agree_tac [p.x19,q.x19,w,x4,y4,Ad,q4,p.x24,q.x24,AL,q5,p.x25,q.x25,blocks,L,len]) ⟨_,by taint_decide⟩

private theorem loopPub {a b u v : State} (la : BoundedLay a) (lb : BoundedLay b)
    (pub : gatherPub a b) (hu : Header a u) (hv : Header b v) (cu : Cursors a u) (cv : Cursors b v) :
    Fragment.LoopPub u v := by
  have bytes := descriptorBytes_agree la pub cu.ds cu.n (hu.toLocalMem.agree la.bds) (hv.toLocalMem.agree lb.bds)
  obtain ⟨_,_,_,_,_,_,q6,q7,qsp,_,d,len,_,_⟩ := pub
  have w : base a = base b := by simp only [base,qsp]
  have bl : blocks a = blocks b := by simp only [blocks,L,len]
  refine ⟨hu.sp.trans (w.trans hv.sp.symm),cu.ds.trans (q6.trans cv.ds.symm),
    congrArg BitVec.toNat (cu.n.trans (q7.trans cv.n.symm)),?_,cu.d.trans (d.trans cv.d.symm),?_,bytes⟩
  · rw [cu.key,cv.key,w]
  · rw [cu.auth,cv.auth,textOff,textOff,bl,w]

theorem body_rel (hash : Hash16Ok) (v : GcmImpl) (scratch : v.ctr.scratch = 0)
    {a b : State} (la : BoundedLay a) (lb : BoundedLay b)
    (ra : recordWithin 224 a) (rb : recordWithin 224 b) (pub : gatherPub a b) :
    RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b)) (Medium.body v.callees) TT := by
  obtain ⟨ai,aa,an⟩ := ra
  obtain ⟨bi,ba,bn⟩ := rb
  have preRel := prefix_rel la lb an bn pub
  have lp := fun {u w : State} => @loopPub a b u w la lb pub
  obtain ⟨key,rounds,nonce,_,_,_,_,_,sp,_,_,len,tag,_⟩ := pub
  have bw : base a = base b := by simp only [base,sp]
  have bl : blocks a = blocks b := by simp only [blocks,L,len]
  have k : K a = K b := key
  unfold Medium.body
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (Fast.RelCT.assoc' preRel) (VG.WP.assoc' (prefix_ok la an aa))
    (VG.WP.assoc' (prefix_ok lb bn ba)) ?_
  intro e f ⟨ha,autha,za,acca⟩ ⟨hb,authb,zb,accb⟩
  have pa := preKeys la ai an ha za
  have pb := preKeys lb bi bn hb zb
  have ps : e.sp = f.sp := ha.sp.trans (bw.trans hb.sp.symm)
  have pbr : MediumKeysPre (base a) (K a) (a.gpr .x1).toNat (blocks a) f := by
    simpa only [bw,k,rounds,bl] using pb
  have keys := mediumKeys_rel v scratch pa pbr ps (ha.x23.trans (nonce.trans hb.x23.symm))
  have kc : RelCT isa (Eq2 e f) (.seq (Medium.keys v.callees) (.block Medium.cursors)) TT := by
    refine rel_seq keys (mediumKeys_ok v scratch pa) (mediumKeys_ok v scratch pb) ?_
    intro x y hx hy
    exact rel_taint [] (hx.sp.trans (ps.trans hy.sp.symm)) (by agree_tac []) ⟨_,by taint_decide⟩
  apply VG.RelCT.assoc
  refine rel_seq kc (ready v scratch la ai an ha autha za acca) (ready v scratch lb bi bn hb authb zb accb) ?_
  intro x y hx hy
  have px := loopPre la hx.toLocalMem hx.toCursors an
  have py := loopPre lb hy.toLocalMem hy.toCursors bn
  refine rel_seq (Fragment.shortLoop_rel px py (lp hx.toHeader hy.toHeader hx.toCursors hy.toCursors))
    (Fragment.shortLoop_ok x px) (Fragment.shortLoop_ok y py) ?_
  intro u w hu hw
  exact mediumFinish_rel hash (loopFinish la an aa hx hu).1 (bw ▸ (loopFinish lb bn ba hy hw).1) key tag

end VG.Proof.AesGcm.AArch64.DirectGather.Mid
