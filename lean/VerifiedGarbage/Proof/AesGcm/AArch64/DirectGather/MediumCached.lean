module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLoopEnd
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumBody
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! Use the contiguous caller's power table after the medium fragment has written ciphertext. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather

/-- This body is called under a 48-byte descriptor adapter. The original third stack
argument is 64 bytes above the stack pointer passed to the medium body. -/
structure CachedInput (o : State) (P : Addr) : Prop where
  rdSlot : InRegions (o.rd ++ o.wr) (o.sp+64#64) 8
  slot : o.mem.readW (o.sp+64#64) 64 = P
  slotWork : (⟨o.sp+64#64,8⟩ : Region).Disjoint (scratch o)
  slotDst : (⟨o.sp+64#64,8⟩ : Region).Disjoint (dR o)
  read : Covers [⟨P,128⟩] (o.rd ++ o.wr)
  work : (⟨P,128⟩ : Region).Disjoint (scratch o)
  dst : (⟨P,128⟩ : Region).Disjoint (dR o)
  repr : Spec.Gcm.Powers8Repr o.mem P (Spec.Gcm.ctxH o.mem (K o))

theorem loadPowers {o s t : State} {extra : List Region} (l : BoundedLay o extra)
    {P : Addr} (key : CachedInput o P) (hn : L o ≤ 224) (al : AL o ≤ 16) (h : Ready o s)
    (cur : Fragment.AtDesc s (Fragment.num s) t) :
    WP isa (.block [.ldrSp .x5 (Medium.work+48+16)]) t fun u =>
      MediumFinishPre o u (base o) (14-blocks o) ∧ ShortPowers u (base o) (K o) Medium.work ∧
      u.gpr .x5 = P := by
  obtain ⟨pre,fr⟩ := loopFinish l hn al h cur
  have mem : Frame [scratch o,dR o] o.mem t.mem :=
    (singletonFrame h.frame (List.mem_cons_self ..) (fun _ => id)).trans fr
  have slot : base o + 816#64 = o.sp+64#64 := by
    change (o.sp-752#64)+816#64=o.sp+64#64
    rw [show (816#64:Addr) = 752#64+64#64 from rfl,← BitVec.add_assoc,BitVec.sub_add_cancel]
  have ptr : InRegions (t.rd ++ t.wr) (t.sp+816#64) 8 := by
    rw [pre.sp,slot,cur.rd,cur.wr]
    exact h.toLocalMem.read _ _ key.rdSlot
  have addr : t.mem.readW (t.sp+816#64) 64 = P := by
    rw [pre.sp,slot]
    exact (mem.readW (r := ⟨o.sp+64#64,8⟩) (Region.contains_self _ _)
      (by intro r hr; rcases List.mem_cons.mp hr with rfl|hr
          · exact key.slotWork
          · exact List.mem_singleton.mp hr ▸ key.slotDst) (by decide)).trans key.slot
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrSp (off := 816) (by decide) ptr,WP.block_nil ?_⟩
  have g : (t.write .x .x5 (t.mem.readW (t.sp+816#64) 64)).gpr .x5 = P := by
    simpa only [gpr_write,ite_true,BitVec.setWidth_eq] using addr
  refine ⟨{pre with},⟨?_,?_,?_⟩,g⟩
  · rw [g,rd_write,wr_write,cur.rd,cur.wr]; exact key.read.trans h.toLocalMem.read
  · rw [g]; exact key.work
  · rw [g,mem_write,pre.hashKey]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => mem.bytes (R := ⟨P,128⟩)
      (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr
          · exact key.work
          · exact List.mem_singleton.mp hr ▸ key.dst)
      (by change (128:Nat) ≤ 2^64; decide) hi) key.repr

theorem cachedBody_ok (v : GcmImpl) (scratch : v.ctr.scratch = 0) (hash : Hash16WithOk) (s : State)
    {extra : List Region} (l : BoundedLay s extra) {P : Addr} (pw : CachedInput s P)
    (iv : NL s = 12) (al : AL s ≤ 16) (hn : L s ≤ 224) :
    WP isa (Medium.bodyCached v.callees) (allocated Medium.work s) fun t => gatherPost s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = base s := by
  refine bodyWith_ok v scratch _ s l iv al hn ?_
  intro t z r done
  refine WP.seq ((loadPowers l pw hn al r done).mono ?_)
  rintro u ⟨finish,tab,_⟩
  exact (mediumFinishWith_ok (cached := true) hash s u _ _ finish (fun _ => tab)).mono fun _ ⟨post,abi,sp,_,_,_⟩ => ⟨post,abi,sp⟩

theorem cachedBody_rel (v : GcmImpl) (scratch : v.ctr.scratch = 0) (hash : Hash16WithOk)
    {a b : State} {ea eb : List Region} (la : BoundedLay a ea) (lb : BoundedLay b eb)
    {P : Addr} (ap : CachedInput a P) (bp : CachedInput b P)
    (ra : recordWithin 224 a) (rb : recordWithin 224 b) (pub : gatherPub a b) :
    RelCT isa (Eq2 (allocated Medium.work a) (allocated Medium.work b)) (Medium.bodyCached v.callees) TT := by
  refine bodyWith_rel _ v scratch la lb ra rb pub ?_
  intro x y u w hx hy hu hw
  obtain ⟨_,aa,an⟩ := ra
  obtain ⟨_,ba,bn⟩ := rb
  obtain ⟨key,_,_,_,_,_,_,_,sp,_,_,_,tag,_⟩ := pub
  have bw : base a = base b := by simp only [base,sp]
  have usp := (loopFinish la an aa hx hu).1.sp
  have wsp := (loopFinish lb bn ba hy hw).1.sp
  refine rel_seq (rel_taint [] (usp.trans (bw.trans wsp.symm)) (by agree_tac []) ⟨_,by taint_decide⟩)
    (loadPowers la ap an aa hx hu) (loadPowers lb bp bn ba hy hw) ?_
  rintro m n ⟨fin,tab,mp⟩ ⟨gin,gab,np⟩
  exact mediumFinishWith_rel (cached := true) hash fin (bw ▸ gin) key tag (fun _ => tab) (fun _ => bw ▸ gab) (fun _ => mp.trans np.symm)

end VG.Proof.AesGcm.AArch64.DirectGather.Mid
