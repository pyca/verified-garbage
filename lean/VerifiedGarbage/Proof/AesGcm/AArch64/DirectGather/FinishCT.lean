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

private def loadTag (tagOff : Nat) : List Instr :=
  [.vop (.rev .rev64b .v16 .v16),.ldrq .v0 .x19 streamO,.vop (.logic .eor .v16 .v16 .v0),
    .ldrSp .x10 tagOff]

private theorem tagPtr_ok {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) (s : State) (W : Addr) (w : s.gpr .x19 = W)
    (read : InRegions (s.rd ++ s.wr) W 16)
    (ptr : InRegions (s.rd ++ s.wr) (s.sp+BitVec.ofNat 64 tagOff) 8) :
    WP isa (.block (loadTag tagOff)) s fun t => t.gpr .x10 = s.mem.readW (s.sp+BitVec.ofNat 64 tagOff) 64 ∧
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
  refine ⟨_,exec_ldrSp (off := tagOff) (by rcases off with rfl|rfl <;> decide) ptr,WP.block_nil ?_⟩
  simp only [gpr_write,ite_true,reduceCtorEq,ite_false,gpr_setV,sp_setV,sp_write,mem_setV,
    BitVec.setWidth_eq,w,and_self]

private abbrev endPrefix (cached : Bool) (tagOff : Nat) := shortLengths ++ shortHashWith authO (shortCore cached) ++ loadTag tagOff
private abbrev endTail := [Instr.strq .v16 .x10 0] ++ Impl.AesGcm.AArch64.restore

private theorem prefix_ok {cached : Bool} {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) {d : ShortOutput} (hash : CoreOk cached) {o s : State} {W : Addr} {i : Nat} (p : ShortFinishPreFor o s W i d tagOff) (powers : cached = true → ShortPowers s W (K o)) :
    WP isa (.block (endPrefix cached tagOff)) s fun t => t.gpr .x10 = d.tag ∧ t.gpr .x19 = W ∧ t.sp = W := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine (shortLengths_ok s p.x19 p.work p.x24 p.x26 (o.gpr .x5).isLt d.len.isLt).mono ?_
  intro l pl
  obtain ⟨_, lf, regs, lsp, lrd, lwr, _⟩ := pl
  have lw : Covers [⟨W,shortWork⟩] l.wr := lwr ▸ p.work
  have lh : Covers [⟨K o+240#64,16⟩] (l.rd ++ l.wr) := by rw [lrd,lwr]; exact p.key
  have subL : Region.Sub ⟨W+336#64,16⟩ ⟨W,shortWork⟩ := Offset.sub_base _ (by decide)
  have subY : Region.Sub ⟨W+352#64,16⟩ ⟨W,shortWork⟩ := Offset.sub_base _ (by decide)
  refine (shortHashWith_ok hash l W (K o) ((regs _ (by decide)).trans p.x19) ((regs _ (by decide)).trans p.x21)
    lw lh (p.keyWork.sub_right subY) (fun h => (powers h).frame lf subL
      (p.keyWork.sub_right subL) (regs .x5 (by decide)) lrd lwr)).mono ?_
  intro h ⟨_, hf, hx, hsp, hrd, hwr⟩
  have sp := hsp.trans (lsp.trans p.sp)
  refine (tagPtr_ok off h W hx (by rw [hrd,hwr,lrd,lwr]; simpa only [BitVec.add_zero] using (
    in_left (rd := s.rd) (in_off (d := 0) (n := 16) p.work (by decide) (by decide))))
    (by rw [sp,hrd,hwr,lrd,lwr]; exact p.ptr)).mono ?_
  intro t ⟨tp,tx,ts⟩
  refine ⟨?_,tx,ts.trans sp⟩
  rw [tp, sp, hf.readW (r := ⟨W+BitVec.ofNat 64 tagOff,8⟩) (Region.contains_self _ _) (by
    simpa only [List.mem_singleton,forall_eq] using (Offset.disjoint W (d := tagOff) (n := 8) (e := 352) (k := 16)
      (.inr (by omega)) (by omega) (by decide))) (by decide),
    lf.readW (r := ⟨W+BitVec.ofNat 64 tagOff,8⟩) (Region.contains_self _ _) (by
    simpa only [List.mem_singleton,forall_eq] using (Offset.disjoint W (d := tagOff) (n := 8) (e := 336) (k := 16)
      (.inr (by omega)) (by omega) (by decide))) (by decide),p.tagAddr]

theorem shortFinishUsing_rel {cached : Bool} {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) {da db : ShortOutput} (hash : CoreOk cached) {a b s t : State} {W : Addr} {i j : Nat}
    (p : ShortFinishPreFor a s W i da tagOff) (q : ShortFinishPreFor b t W j db tagOff) (k : K a = K b) (tag : da.tag = db.tag)
    (pc : cached = true → ShortPowers s W (K a)) (qc : cached = true → ShortPowers t W (K b))
    (powerEq : cached = true → s.gpr .x5 = t.gpr .x5) :
    RelCT isa (Eq2 s t) (.block (shortLengths ++ shortHashWith authO (shortCore cached) ++ shortTagAt tagOff ++ Impl.AesGcm.AArch64.restore)) TT := by
  have eq : shortLengths ++ shortHashWith authO (shortCore cached) ++ shortTagAt tagOff ++ Impl.AesGcm.AArch64.restore =
      endPrefix cached tagOff ++ endTail := by simp only [shortTagAt,writeTag,endPrefix,endTail,loadTag,List.append_assoc,List.cons_append,
        List.nil_append]
  rw [eq]
  apply RelCT.block_split
  have pre : RelCT isa (Eq2 s t) (.block (endPrefix cached tagOff)) TT := by
    cases cached with
    | false =>
      exact rel_taint [.x19,.x21] (p.sp.trans q.sp.symm)
        (by agree_tac [p.x19,q.x19,p.x21,q.x21,k]) (by rcases off with rfl|rfl <;> exact ⟨_,by taint_decide⟩)
    | true =>
      have eq5 := powerEq rfl
      exact rel_taint [.x5,.x19,.x21] (p.sp.trans q.sp.symm)
        (by agree_tac [p.x19,q.x19,p.x21,q.x21,k,eq5]) (by rcases off with rfl|rfl <;> exact ⟨_,by taint_decide⟩)
  refine rel_seq pre (prefix_ok off hash p pc) (prefix_ok off hash q qc) ?_
  intro u v ⟨u10,u19,us⟩ ⟨v10,v19,vs⟩
  exact rel_taint [.x10,.x19] (us.trans vs.symm) (by agree_tac [u10,v10,u19,v19,tag]) ⟨_,by taint_decide⟩

theorem shortFinishAt_rel {tagOff : Nat} (off : tagOff = 376 ∨ tagOff = 384) {da db : ShortOutput} (hash : HashEightOk) {a b s t : State} {W : Addr} {i j : Nat}
    (p : ShortFinishPreFor a s W i da tagOff) (q : ShortFinishPreFor b t W j db tagOff) (k : K a = K b) (tag : da.tag = db.tag) :
    RelCT isa (Eq2 s t) (.block (shortLengths ++ shortHash authO ++ shortTagAt tagOff ++ Impl.AesGcm.AArch64.restore)) TT :=
  shortFinishUsing_rel (cached := false) off hash p q k tag (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)

theorem shortFinish_rel (hash : HashEightOk) {a b s t : State} {W : Addr} {i j : Nat}
    (p : ShortFinishPre a s W i) (q : ShortFinishPre b t W j) (k : K a = K b) (tag : Tg a = Tg b) :
    RelCT isa (Eq2 s t) (.block (shortLengths ++ shortHash authO ++ shortTagOut ++ Impl.AesGcm.AArch64.restore)) TT :=
  shortFinishAt_rel (.inr rfl) hash p q k tag

end VG.Proof.AesGcm.AArch64.DirectGather
