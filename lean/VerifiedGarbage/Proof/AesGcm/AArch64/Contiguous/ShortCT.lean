module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Short
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared

/-! Every branch and address of the short contiguous record depends only
on the public byte counts, round count, pointers and stack slots. -/

public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Short

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.Contiguous VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

theorem frame_rel (hash : HashEightOk) {a b : State} (ca : Caller a) (cb : Caller b)
    (ai : NL a = 12) (bi : NL b = 12) (aa : AL a ≤ 16) (ba : AL b ≤ 16)
    (an : len a ≤ 96) (bn : len b ≤ 96) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) shortFrame TT := by
  apply RelCT.alloc (R := TT)
  suffices body : RelCT isa (Eq2 (allocated shortWork a) (allocated shortWork b)) shortRecordBody TT from
    body.mono (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)
  obtain ⟨q0,q1,q2,_,q4,q5,q6,q7,qsp,stk⟩ := pub
  have w : base a = base b := by simp only [base,qsp]
  have n : len a = len b := congrArg BitVec.toNat (stk 0 (by decide))
  have ce : count a = count b := by rw [count,count,n]
  have al : AL a = AL b := congrArg BitVec.toNat q5
  have preRel : RelCT isa (Eq2 (allocated shortWork a) (allocated shortWork b))
      (.seq (.block (shortSetupAt shortWork)) (.seq (.block shortZero) shortAad)) TT := by
    refine rel_seq (rel_taint [] w (by agree_tac []) ⟨_,by taint_decide⟩) (enter ca an) (enter cb bn) ?_
    intro u v ⟨p,p4⟩ ⟨q,q4'⟩
    exact rel_taint [.x4,.x19,.x24,.x25] (p.sp.trans (w.trans q.sp.symm))
      (by agree_tac [p4,q4',Ad,q4,p.x19,q.x19,p.x24,q.x24,p.x25,q.x25,al,w,n]) ⟨_,by taint_decide⟩
  unfold shortRecordBody
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (Fast.RelCT.assoc' preRel) (VG.WP.assoc' (prefix_ok ca an aa))
    (VG.WP.assoc' (prefix_ok cb bn ba)) ?_
  intro e f ⟨p,pin⟩ ⟨q,qin⟩
  apply VG.RelCT.assoc
  refine rel_seq (rel_taint [.x7,.x19,.x21,.x22,.x23,.x25] (p.sp.trans (w.trans q.sp.symm))
    (by agree_tac [p.x7,q.x7,q7,p.x19,q.x19,p.x21,q.x21,p.x22,q.x22,p.x23,q.x23,p.x25,q.x25,K,Nn,q0,q1,q2,w,n])
    ⟨_,by taint_decide⟩) (ready ca ai an p pin) (ready cb bi bn q qin) ?_
  intro u v hu hv
  refine rel_seq (rel_taint [.x1,.x2,.x3,.x6,.x26] (hu.sp.trans (w.trans hv.sp.symm))
    (by agree_tac [hu.key,hv.key,hu.dst,hv.dst,hu.auth,hv.auth,hu.x6,hv.x6,hu.x26,hv.x26,buffers,Src,q6,q7,ce,w,n])
    ⟨_,by taint_decide⟩)
    (Fragment.directPiece_ok (pieceLayout ca an hu) hu.x6 hu.x26 hu.key hu.dst hu.auth)
    (Fragment.directPiece_ok (pieceLayout cb bn hv) hv.x6 hv.x26 hv.key hv.dst hv.auth) ?_
  intro x y hx hy
  exact shortFinishAt_rel (.inl rfl) hash (finishPre ca an aa hu hx) (w ▸ finishPre cb bn ba hv hy) q0 (stk 1 (by decide))

end VG.Proof.AesGcm.AArch64.Contiguous.Short
