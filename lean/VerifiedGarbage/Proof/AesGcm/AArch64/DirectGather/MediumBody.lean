module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLoopEnd
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumKeys
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Compose the CTR call and direct fragment encryption inside the bounded gather frame. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid
open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt inc32 zeros)
open VG.AArch64.Scrub

theorem preKeys {o s : State} {extra : List Region} (l : BoundedLay o extra) (iv : NL o = 12) (hn : L o ≤ 224)
    (h : Header o s) (zero : bytesAt s.mem (base o+224) 256 = zeros 256) :
    MediumKeysPre (base o) (K o) (o.gpr .x1).toNat (blocks o) s := by
  have bound : blocks o ≤ 14 := by unfold blocks; omega
  have keyR : Covers [kR .plain o] (s.rd ++ s.wr) := Covers.of_mem fun r hr => by
    rw [h.rd,l.rd,List.mem_singleton.mp hr]; simp
  have nonceR : Covers [⟨Nn o,12⟩] (s.rd ++ s.wr) := by
    rw [h.rd,← iv]; exact Covers.of_mem fun r hr => List.mem_append_left _ (by
      rw [l.rd,List.mem_singleton.mp hr]; simp [nR])
  refine ⟨h.x19,h.x21,by simpa using h.x22,h.x25,l.hR,by omega,?_,h.scratchWr,
    covers_prefix keyR (by decide),(l.bk.sub_left (scratch_sub o)).symm.sub_left (Region.sub_prefix (by decide)),?_,?_,?_⟩
  · have le : 752 ≤ o.sp.toNat := by have := l.w₁; omega
    unfold base
    rw [BitVec.toNat_sub_of_le (show BitVec.ofNat 64 Medium.work ≤ o.sp from BitVec.le_def.mpr le)]
    change o.sp.toNat - 752 + 752 ≤ 2^64
    have := o.sp.isLt; omega
  · rw [h.x23]; exact in_off nonceR (by decide) (by decide)
  · rw [h.x23]; exact in_off nonceR (by decide) (by decide)
  · intro i hi
    rw [blockAt,Proof.Cmac.Stream.bytesAt_offset _ _ (show 16*i + 16 ≤ 256 by omega),zero]
    simp only [zeros,List.drop_replicate,List.take_replicate,Nat.min_eq_left (show 16 ≤ 256-16*i by omega)]
    exact Proof.Gcm.ofBytes_zeros16

private theorem keyCipher {o s : State} {extra : List Region} (l : BoundedLay o extra) (h : LocalMem o s) :
    ciphOf s.mem (K o) (o.gpr .x1).toNat = shortCipher o := by
  let n := (o.gpr .x1).toNat
  have small : n ≤ 14 := by rcases l.hR with e|e|e <;> simp only [n,e] <;> decide
  have sub : (⟨K o,16*(n+1)⟩ : Region).Sub (kR .plain o) := Region.sub_prefix (by change 16*(n+1) ≤ 256; omega)
  unfold ciphOf
  rw [bytesAt_frame h.frame (by simpa only [List.mem_singleton,forall_eq] using
    (l.bk.sub_left (scratch_sub o)).symm.sub_left sub) (by change 16*(n+1) ≤ 2^64; omega)]
  rfl

private theorem keyNonce {o s : State} {extra : List Region} (l : BoundedLay o extra) (iv : NL o = 12) (h : Header o s) :
    Counters.jZero s = shortJ0 o := by
  unfold Counters.jZero Counters.nonce shortJ0
  rw [h.x23,Proof.Gcm.j0_12 _ (by rw [Proof.Cmac.bytesAt_length,iv]),← iv]
  rw [bytesAt_frame h.frame (by simpa only [List.mem_singleton,forall_eq] using
    (l.bn.sub_left (scratch_sub o)).symm) (Nat.le_of_lt (o.gpr .x3).isLt)]

theorem ready {o s : State} (v : GcmImpl) (v0 : v.ctr.scratch = 0) {extra : List Region} (l : BoundedLay o extra)
    (iv : NL o = 12) (hn : L o ≤ 224) (h : Header o s)
    (input : bytesAt s.mem (ghBase o) 256 = aadLayout o)
    (zero : bytesAt s.mem (base o+224) 256 = zeros 256)
    (acc : bytesAt s.mem (base o+736) 16 = zeros 16) :
    WP isa (.seq (Medium.keys v.callees) (.block Medium.cursors)) s (Ready o) := by
  have hc : blocks o ≤ 14 := by unfold blocks; omega
  refine WP.seq ((mediumKeys_ok v v0 (preKeys l iv hn h zero)).mono ?_)
  intro k hk
  have localK : LocalMem o k := ⟨h.frame.trans (hk.frame.sub (by
    intro r hr; refine ⟨scratch o,List.mem_singleton_self _,?_⟩
    rcases List.mem_cons.mp hr with rfl|hr
    · exact Region.sub_prefix (by decide)
    · obtain rfl := List.mem_singleton.mp hr; exact Offset.sub_base _ (by decide))),
    hk.rd.trans h.rd,hk.wr.trans h.wr⟩
  have sp := hk.sp.trans h.sp
  have k19 := (hk.kept .x19 (by decide)).trans h.x19
  have k25 := (hk.kept .x25 (by decide)).trans h.x25
  have saved := h.saved.frame hk.frame (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · obtain rfl := List.mem_singleton.mp hq; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  refine (cursors_ok hc k k19 k25 (by rw [sp]; exact localK.argRead l 0 (by decide))).mono ?_
  intro t ⟨key,dst,auth,x6,x7,g,m,ts,tr,tw⟩
  have reg (r : Reg) (a : r ∉ [.x1,.x2,.x3,.x6,.x7]) (b : r ∈ medKept) := (g r a).trans (hk.kept r b)
  have header : Header o t := ⟨⟨m ▸ localK.frame,tr.trans localK.rd,tw.trans localK.wr⟩,ts.trans sp,
    m ▸ saved,(g _ (by decide)).trans k19,
    (reg _ (by decide) (by decide)).trans h.x21,(reg _ (by decide) (by decide)).trans h.x22,
    (reg _ (by decide) (by decide)).trans h.x23,(reg _ (by decide) (by decide)).trans h.x24,
    (g _ (by decide)).trans k25,(reg _ (by decide) (by decide)).trans h.x26,
    x6.trans (hk.desc.trans h.x6),x7.trans (hk.count.trans h.x7)⟩
  have kc := keyCipher l h.toLocalMem
  have ns := keyNonce l iv h
  refine ⟨header,⟨dst.trans (by rw [sp]; exact localK.arg l 0 (by decide)),auth,key,header.x6,header.x7⟩,
    by simpa only [m,kc,ns,medD,show (224:Addr)=224#64 by decide] using hk.mask,?_,?_,?_⟩
  · intro j hj
    rw [m]; simpa only [kc,ns] using hk.stream j (by unfold blocks; omega)
  · rw [m,bytesAt_frame hk.frame (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · obtain rfl := List.mem_singleton.mp hr; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide), input]
  · rw [m,blockAt,bytesAt_frame hk.frame (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · obtain rfl := List.mem_singleton.mp hr; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide),acc,Proof.Gcm.ofBytes_zeros16]

theorem bodyWith_ok (v : GcmImpl) (v0 : v.ctr.scratch = 0) (endCode : Prog isa) (s : State)
    {extra : List Region} (l : BoundedLay s extra) (iv : NL s = 12) (al : AL s ≤ 16) (hn : L s ≤ 224)
    (endOk : ∀ {t z : State}, Ready s t → Fragment.AtDesc t (Fragment.num t) z →
      WP isa endCode z fun u => gatherPost s u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.sp = base s) :
    WP isa (Medium.bodyWith v.callees endCode) (allocated Medium.work s) fun t => gatherPost s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = base s := by
  have front := prefix_ok l hn al
  unfold Medium.bodyWith
  refine WP.seq ((WP.seq_iff.mp front).mono (fun _ w => WP.seq ((WP.seq_iff.mp w).mono (fun _ w => WP.seq (w.mono ?_)))))
  intro q ⟨header,input,zero,acc⟩
  have key := ready v v0 l iv hn header input zero acc
  refine WP.seq ((WP.seq_iff.mp key).mono (fun _ w => WP.seq (w.mono ?_)))
  intro t r
  refine WP.seq ((Fragment.shortLoop_ok t (loopPre l r.toLocalMem r.toCursors hn)).mono ?_)
  intro z done
  exact endOk r done

theorem body_ok (v : GcmImpl) (v0 : v.ctr.scratch = 0) (hash : Hash16Ok) (s : State)
    (l : BoundedLay s) (iv : NL s = 12) (al : AL s ≤ 16) (hn : L s ≤ 224) :
    WP isa (Medium.body v.callees) (allocated Medium.work s) fun t => gatherPost s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = base s := by
  refine bodyWith_ok v v0 _ s l iv al hn ?_
  intro t z r done
  have finish := (loopFinish l hn al r done).1
  exact (mediumFinish_ok hash s z (base s) _ finish).mono fun _ ⟨post,abi,sp,_,_,_⟩ => ⟨post,abi,sp⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Mid
