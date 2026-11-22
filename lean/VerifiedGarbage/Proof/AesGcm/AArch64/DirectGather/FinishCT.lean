module

meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishSpec
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! The tag address loaded from the stack is public. Split just after its
load so the trace comparison can use the original gather tag pointer. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.Gcm.AArch64.Pmull (exec_rev64b exec_ldrq exec_eor)
open VG.Proof.AesGcm.AArch64 (rel_seq rel_taint Eq2 TT)

private def loadTag : List Instr :=
  [.vop (.rev .rev64b .v16 .v16),.ldrq .v0 .x19 streamO,.vop (.logic .eor .v16 .v16 .v0),
    .ldrSp .x10 (shortWork+16)]

private theorem tagPtr_ok (s : State) (W : Addr) (w : s.gpr .x19 = W)
    (read : InRegions (s.rd ++ s.wr) W 16)
    (ptr : InRegions (s.rd ++ s.wr) (s.sp+384#64) 8) :
    WP isa (.block loadTag) s fun t => t.gpr .x10 = s.mem.readW (s.sp+384#64) 64 ∧
      t.gpr .x19 = W ∧ t.sp = s.sp := by
  unfold loadTag
  rw [WP.block_cons_iff]
  refine ⟨_,exec_rev64b _ _ _,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrq (off := streamO) (by decide) (by decide) ?_,?_⟩
  · simpa only [streamO,gpr_setV,w,BitVec.add_zero,rd_setV,wr_setV] using read
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrSp (off := shortWork+16) (by decide) ptr,WP.block_nil ?_⟩
  simp only [gpr_write,ite_true,reduceCtorEq,ite_false,gpr_setV,sp_setV,sp_write,mem_setV,
    BitVec.setWidth_eq,w,and_self]
  exact ⟨rfl,trivial⟩

private abbrev endPrefix := shortLengths ++ shortHash authO ++ loadTag
private abbrev endTail := [Instr.strq .v16 .x10 0] ++ Impl.AesGcm.AArch64.restore

private theorem prefix_ok (hash : HashEightOk) {o s : State} {W : Addr} {i : Nat} (p : ShortFinishPre o s W i) :
    WP isa (.block endPrefix) s fun t => t.gpr .x10 = Tg o ∧ t.gpr .x19 = W ∧ t.sp = W := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (shortLengths_ok s p.x19 p.work p.x24 p.x26 (o.gpr .x5).isLt (stackArg o 1).isLt).mono ?_
  intro l pl
  obtain ⟨_, lf, regs, lsp, lrd, lwr, _⟩ := pl
  have lw : Covers [⟨W,shortWork⟩] l.wr := lwr ▸ p.work
  have lh : Covers [⟨K o+240#64,16⟩] (l.rd ++ l.wr) := by rw [lrd,lwr]; exact p.key
  have subY : Region.Sub ⟨W+352#64,16⟩ ⟨W,shortWork⟩ := Offset.sub_base _ (by decide)
  refine (shortHash_ok hash l W (K o) ((regs _ (by decide)).trans p.x19) ((regs _ (by decide)).trans p.x21)
    lw lh (p.keyWork.sub_right subY)).mono ?_
  intro h ⟨_, hf, hx, hsp, hrd, hwr⟩
  have sp := hsp.trans (lsp.trans p.sp)
  refine (tagPtr_ok h W hx (by rw [hrd,hwr,lrd,lwr]; simpa only [BitVec.add_zero] using (
    in_left (rd := s.rd) (in_off (d := 0) (n := 16) p.work (by decide) (by decide))))
    (by rw [sp,hrd,hwr,lrd,lwr]; exact p.ptr)).mono ?_
  intro t ⟨tp,tx,ts⟩
  refine ⟨?_,tx,ts.trans sp⟩
  rw [tp, sp, hf.readW (r := ⟨W+384#64,8⟩) (Region.contains_self _ _) (by
    simpa only [List.mem_singleton,forall_eq] using (Offset.disjoint W (d := 384) (n := 8) (e := 352) (k := 16)
      (.inr (by decide)) (by decide) (by decide))) (by decide),
    lf.readW (r := ⟨W+384#64,8⟩) (Region.contains_self _ _) (by
    simpa only [List.mem_singleton,forall_eq] using (Offset.disjoint W (d := 384) (n := 8) (e := 336) (k := 16)
      (.inr (by decide)) (by decide) (by decide))) (by decide),p.tagAddr]

theorem shortFinish_rel (hash : HashEightOk) {a b s t : State} {W : Addr} {i j : Nat}
    (p : ShortFinishPre a s W i) (q : ShortFinishPre b t W j) (k : K a = K b) (tag : Tg a = Tg b) :
    RelCT isa (Eq2 s t) (.block (shortLengths ++ shortHash authO ++ shortTagOut ++ Impl.AesGcm.AArch64.restore)) TT := by
  have eq : shortLengths ++ shortHash authO ++ shortTagOut ++ Impl.AesGcm.AArch64.restore =
      endPrefix ++ endTail := by simp only [shortTagOut,writeTag,endPrefix,endTail,loadTag,List.append_assoc,List.cons_append,
        List.nil_append]
  rw [eq]
  apply RelCT.block_split
  refine rel_seq (rel_taint [.x19,.x21] (p.sp.trans q.sp.symm)
    (by agree_tac [p.x19,q.x19,p.x21,q.x21,k]) ⟨_,by taint_decide⟩) (prefix_ok hash p) (prefix_ok hash q) ?_
  intro u v ⟨u10,u19,us⟩ ⟨v10,v19,vs⟩
  exact rel_taint [.x10,.x19] (us.trans vs.symm) (by agree_tac [u10,v10,u19,v19,tag]) ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.DirectGather
