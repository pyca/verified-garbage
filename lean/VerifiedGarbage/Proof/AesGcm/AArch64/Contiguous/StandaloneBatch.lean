module

-- separate module: Keep the stitched batch and its taint certificate independent of the tail and per-message proofs.

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandalonePowers
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.BatchesCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.DirectBatches
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! Build the stitched loop's table from the caller's key powers. The
counter/hash loop and its cursor result are those of the piece-based caller. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.Stitch (pwTbl)
open VG.Proof.Gcm.AArch64.Stitch (BatchArgs BatchIn BatchOut Gh8Ok batchCode batchCode_ok)

theorem cachedBatch_ok {wn R n : Nat} {Ctx St W SP D O P : Addr} {s : State}
    (h : BatchIn wn Ctx St W SP D O R n s) (L : Lay wn Ctx St W) (hn : 128≤n)
    (key : BatchPowers wn Ctx W P s) (gh : Gh8Ok) (forward : Bool) :
    WP isa (batchCode forward (pwTbl (wn+48))) s (BatchOut Ctx St W D O R n s) := by
  apply batchCode_ok h L hn gh forward
  intro t a regs
  have p := key.after (t := t) (regs.mem ▸ Frame.refl _ _) regs.sp regs.rd regs.wr
  refine (Stitch.pwTbl_ok (k := wn+48) p.offset a.env p.ptr p.slot p.reads p.repr).mono ?_
  rintro u ⟨table,frame,gpr,sp,rd,wr⟩
  refine ⟨?_,?_,fun r _ ne => gpr r ne,sp,rd,wr⟩
  · simpa only [a.env.x19,a.env.x21] using table
  · simpa only [a.env.x19] using frame

/-- The only address loaded from memory by the table setup is the public
powers pointer. Every subsequent lookup is at a fixed offset from it. -/
theorem cachedBatch_rel {wn R n : Nat} {Ctx St W SP D O P : Addr} {s t : State}
    (a : BatchIn wn Ctx St W SP D O R n s) (b : BatchIn wn Ctx St W SP D O R n t)
    (pa : BatchPowers wn Ctx W P s) (pb : BatchPowers wn Ctx W P t) (forward : Bool) :
    RelCT isa (Eq2 s t) (batchCode forward (pwTbl (wn+48))) TT := by
  apply RelCT.seq_block_append
  refine rel_seq (rel_taint [.x23,.x24,.x26] (a.env.sp.trans b.env.sp.symm)
    (by agree_tac [a.x23,b.x23,a.x24,b.x24,a.x26,b.x26]) ⟨_,by taint_decide⟩)
    (VG.Proof.Gcm.AArch64.Stitch.batchArgs_ok a) (VG.Proof.Gcm.AArch64.Stitch.batchArgs_ok b) ?_
  intro u z ⟨hu,au⟩ ⟨hz,bz⟩
  have pu := pa.after (t := u) (au.mem ▸ Frame.refl _ _) au.sp au.rd au.wr
  have pz := pb.after (t := z) (bz.mem ▸ Frame.refl _ _) bz.sp bz.rd bz.wr
  let regs : List Reg := [.x15,.x19,.x20,.x21,.x22,.x23,.x24,.x26]
  have eq : ∀ r ∈ regs, u.gpr r=z.gpr r := by
    unfold regs
    agree_tac [hu.x15,hz.x15,hu.env.x19,hz.env.x19,hu.env.x20,hz.env.x20,
      hu.env.x21,hz.env.x21,hu.x22,hz.x22,hu.x23,hz.x23,hu.x26,hz.x26,
      au.others .x24 (by decide),bz.others .x24 (by decide),a.x24,b.x24]
  apply Fast.pwTblAligned_relR regs pu.offset _ (hu.env.sp.trans hz.env.sp.symm) eq pu.ptr pu.slot pz.ptr pz.slot
  intro i j sameSp inputs
  apply rel_taint (.x5 :: regs) sameSp inputs
  dsimp only [regs]
  cases forward <;> exact ⟨_,by taint_decide⟩

theorem BatchPowers.afterGh {wn n : Nat} {Ctx St W P Q : Addr} {s t : State}
    (h : BatchPowers wn Ctx W P s) (hw : 768 ≤ wn) (hs : St=W+16#64)
    (g : GhPost s (Ctx+240#64) (St+16#64) Q (W+512#64) n t) : BatchPowers wn Ctx W P t := by
  apply h.after _ g.sp g.rd g.wr
  refine g.frame.sub fun r hr => ⟨_,List.mem_singleton_self _,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · subst St; rw [BitVec.add_assoc]; exact Lay.wSub (d := 32) (by omega)
  · exact Lay.wSub (d := 512) (by omega)

open VG.Proof.Gcm.AArch64.Stitch (PendingIn BatchesPost batchTest batchesWith_ok)
open VG.Impl.AesGcm.AArch64.DirectGather (batches)

theorem cachedBatches_ok {wn R n : Nat} {Ctx St W SP D O P : Addr} {s : State}
    (v : GcmImpl) (a : BatchIn wn Ctx St W SP D O R n s) (L : Lay wn Ctx St W)
    (pending : PendingIn wn St W O O 0 s) (key : BatchPowers wn Ctx W P s)
    (hs : St=W+16#64) (gh : Gh8Ok) (forward : Bool) :
    WP isa (batches v.callees forward (pwTbl (wn+48))) s (BatchesPost Ctx St W D O O R n 0 s) :=
  batchesWith_ok v a L (fun _ => pending) forward fun hn hu q =>
    cachedBatch_ok hu L hn (key.afterGh a.env.perm.hWn.1 hs q) gh forward

theorem cachedBatches_rel {wn R n : Nat} {Ctx St W SP D O P : Addr} {s t : State}
    (v : GcmImpl) (a : BatchIn wn Ctx St W SP D O R n s) (b : BatchIn wn Ctx St W SP D O R n t)
    (L : Lay wn Ctx St W) (pendA : PendingIn wn St W O O 0 s) (pendB : PendingIn wn St W O O 0 t)
    (pa : BatchPowers wn Ctx W P s) (pb : BatchPowers wn Ctx W P t) (hs : St=W+16#64) (forward : Bool) :
    RelCT isa (Eq2 s t) (batches v.callees forward (pwTbl (wn+48))) TT :=
  DirectGather.Generic.batchesWith_rel v a b L (fun _ => pendA) (fun _ => pendB) forward fun u z x y =>
    cachedBatch_rel u z (pa.afterGh a.env.perm.hWn.1 hs x) (pb.afterGh b.env.perm.hWn.1 hs y) forward

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
