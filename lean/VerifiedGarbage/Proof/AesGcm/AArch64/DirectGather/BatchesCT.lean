module

meta import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather

/-! Only the public batch length, pending ciphertext cursor and accumulator
addresses affect the branch and call traces in the stitched gather path. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesGcm.AArch64 (ghArgs)
open VG.Impl.AesGcm.AArch64.DirectGather (hashO hashPending batches)
open VG.Proof.Gcm.AArch64.Stitch (BatchIn PendingIn batchTest batchCode hashPending_ok GatherLaws)
open VG.Proof.AesGcm.AArch64 (rel_taint rel_seq rel_ite rel_gh Eq2 TT)
variable {Wn R n k : Nat} {Ctx St W SP D O P : Addr} {s t : State}

private theorem batchCode_rel (h : BatchIn Wn Ctx St W SP D O R n s) (g : BatchIn Wn Ctx St W SP D O R n t) :
    RelCT isa (Eq2 s t) batchCode TT :=
  rel_taint [.x19,.x20,.x21,.x22,.x23,.x24,.x26] (h.env.sp.trans g.env.sp.symm)
    (by agree_tac [h.env.x19,g.env.x19,h.env.x20,g.env.x20,h.env.x21,g.env.x21,
      h.x22,g.x22,h.x23,g.x23,h.x24,g.x24,h.x26,g.x26]) ⟨_,by taint_decide⟩

open VG.Proof.Gcm.AArch64.Stitch (pendingCursor pendingGhArgs pendingGhCall batchGuard)

private theorem rel_block_run {is : List Instr} {c : Prog isa} {a b u v : State}
    (p : RelCT isa (Eq2 a b) (.block is) TT) (ra : runBlock isa is a = some u) (rb : runBlock isa is b = some v)
    (after : RelCT isa (Eq2 u v) c TT) : RelCT isa (Eq2 a b) (.seq (.block is) c) TT :=
  rel_seq p (WP.of_runBlock ⟨_,ra,rfl⟩) (WP.of_runBlock ⟨_,rb,rfl⟩) fun _ _ h k => h ▸ k ▸ after

private theorem hashPending_rel (v : GcmImpl) (L : Lay Wn Ctx St W)
    (h : BatchIn Wn Ctx St W SP D O R n s) (g : BatchIn Wn Ctx St W SP D O R n t)
    (ps : PendingIn Wn St W P O k s) (pt : PendingIn Wn St W P O k t) :
    RelCT isa (Eq2 s t) (hashPending v.callees) TT := by
  obtain ⟨a,ra,a2,a3,ar⟩ := pendingCursor h.env ps.slot (h.x26.trans ps.stop) ps.data
  obtain ⟨b,rb,b2,b3,br⟩ := pendingCursor g.env pt.slot (g.x26.trans pt.stop) pt.data
  have sp := ar.sp.trans (h.env.sp.trans (g.env.sp.symm.trans br.sp.symm))
  have envA := h.env.of_regs ar
  have envB := g.env.of_regs br
  refine rel_block_run (rel_taint [.x19] (h.env.sp.trans g.env.sp.symm)
    (by agree_tac [h.env.x19,g.env.x19]) ⟨_,by taint_decide⟩) ra rb ?_
  refine rel_ite (eval_zero a3 (by have := ps.data.lt; omega)) (eval_zero b3 (by have := pt.data.lt; omega))
    (fun _ => rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩) ?_
  intro _
  obtain ⟨u,ru,u0,u1,u4,ur⟩ := pendingGhArgs envA
  obtain ⟨z,rz,z0,z1,z4,zr⟩ := pendingGhArgs envB
  refine rel_block_run (rel_taint [] sp (by agree_tac []) ⟨_,by taint_decide⟩) ru rz ?_
  exact rel_gh v.gh (pendingGhCall L envA (ps.data.of_eq ar.rd ar.wr) a2 a3 u0 u1 u4 ur)
    (pendingGhCall L envB (pt.data.of_eq br.rd br.wr) b2 b3 z0 z1 z4 zr) (ur.sp.trans (sp.trans zr.sp.symm))

private theorem batchAfter {u : State} (h : BatchIn Wn Ctx St W SP D O R n s)
    (g : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r) (sp : u.sp = s.sp)
    (rd : u.rd = s.rd) (wr : u.wr = s.wr) : BatchIn Wn Ctx St W SP D O R n u :=
  ⟨h.env.of_saved g sp rd wr,h.rounds,(g _ (by decide) (by decide)).trans h.x22,
    (g _ (by decide) (by decide)).trans h.x23,(g _ (by decide) (by decide)).trans h.x24,
    (g _ (by decide) (by decide)).trans h.x26,h.src.of_eq rd wr,h.dst.of_eq rd wr,h.apart⟩

private theorem batchEval {a : State} (hn : a.gpr .x9 = batchTest n) :
    isa.eval (.zero .x .x9) a = some (decide (batchTest n = 0)) := by
  change some (a.gpr .x9 == (0 : Addr)) = _
  rw [hn]
  by_cases z : batchTest n = 0
  · rw [z]; rfl
  · rw [beq_eq_false_iff_ne.mpr z,decide_eq_false z]

theorem batches_rel (v : GcmImpl) (h : BatchIn Wn Ctx St W SP D O R n s) (g : BatchIn Wn Ctx St W SP D O R n t)
    (L : Lay Wn Ctx St W) (_gh : GatherLaws) (ps : batchTest n ≠ 0 → PendingIn Wn St W P O k s)
    (pt : batchTest n ≠ 0 → PendingIn Wn St W P O k t) : RelCT isa (Eq2 s t) (batches v.callees) TT := by
  obtain ⟨a,ra,testA,ar⟩ := batchGuard h
  obtain ⟨b,rb,testB,br⟩ := batchGuard g
  have sp := ar.sp.trans (h.env.sp.trans (g.env.sp.symm.trans br.sp.symm))
  have keep (r : Reg) (hr : r ∈ preserved) : r ∉ [.x9] := by
    intro he; obtain rfl := List.mem_singleton.mp he; contradiction
  have ha := batchAfter h (fun r hr _ => ar.others r (keep r hr)) ar.sp ar.rd ar.wr
  have hb := batchAfter g (fun r hr _ => br.others r (keep r hr)) br.sp br.rd br.wr
  refine rel_block_run (rel_taint [] (h.env.sp.trans g.env.sp.symm) (by agree_tac []) ⟨_,by taint_decide⟩) ra rb ?_
  refine rel_ite (batchEval testA) (batchEval testB) (fun _ => rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩) ?_
  intro nz
  have z := of_decide_eq_false nz
  have pa := ps z
  have pb := pt z
  have qa : PendingIn Wn St W P O k a := ⟨ar.mem ▸ pa.slot,pa.stop,pa.data.of_eq ar.rd ar.wr⟩
  have qb : PendingIn Wn St W P O k b := ⟨br.mem ▸ pb.slot,pb.stop,pb.data.of_eq br.rd br.wr⟩
  refine rel_seq (hashPending_rel v L ha hb qa qb)
    (hashPending_ok v L ha.env qa.slot (ha.x26.trans qa.stop) qa.data)
    (hashPending_ok v L hb.env qb.slot (hb.x26.trans qb.stop) qb.data) fun u z p q => ?_
  exact batchCode_rel (batchAfter ha p.saved p.sp p.rd p.wr) (batchAfter hb q.saved q.sp q.rd q.wr)

end VG.Proof.AesGcm.AArch64.DirectGather.Generic
