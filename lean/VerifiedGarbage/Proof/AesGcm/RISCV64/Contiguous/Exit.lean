module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! # The common contiguous seal tag output and RISC-V register restore -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous (exitHead exitCode)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)
open VG.Spec.Aes (bytesAt)

structure ExitArgs (s o : State) (w tag : Addr) : Prop where
  wreg : s.gpr .s0 = w
  sp : s.sp = o.sp
  spAlign : s.sp.toNat % 8 = 0
  slot : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8
  tagPtr : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = tag
  work : Covers [⟨w,2560⟩] (s.rd ++ s.wr)
  workAlign : w.toNat % 8 = 0
  writable : Covers [⟨tag,16⟩] s.wr
  apart : (⟨tag,16⟩ : Region).Disjoint ⟨w,2560⟩
  saved : SavedAt s.mem w o

private theorem load_wp {s o : State} (a : ExitArgs s o w tag) :
    WP isa (.block exitHead) s fun t =>
      t.gpr .s9 = tag ∧ t.gpr .s0 = w ∧ Keeps s t := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun u k => ?_
  refine Steps.wp_ld (a := s.sp + BitVec.ofNat 64 8) (off := 8) (by decide)
    (by rw [k.gpr,BitVec.add_zero]) (Spill.al8 a.spAlign (by decide))
    (by rw [k.rd,k.wr]; exact a.slot) fun t q => WP.block_nil ?_
  exact ⟨q.gpr.trans (k.mem ▸ a.tagPtr),(q.other _ (by decide)).trans ((k.other _ (by decide)).trans a.wreg),
    ⟨q.mem.trans k.mem,q.rd.trans k.rd,q.wr.trans k.wr,q.sp.trans k.sp⟩⟩

theorem exit_wp {s o : State} (a : ExitArgs s o w tag) : WP isa (.block exitCode) s fun t =>
    abiPreserved o t ∧ bytesAt t.mem tag 16 = bytesAt s.mem w 16 ∧
      Frame [⟨tag,16⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold exitCode
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (load_wp a) fun u ⟨tagReg,workReg,k⟩ => ?_
  have work : Covers [⟨w,2560⟩] (u.rd ++ u.wr) := by rw [k.rd,k.wr]; exact a.work
  refine WP.mono (tagOut_at tagReg workReg (covers_prefix work (by decide))
    (k.wr ▸ a.writable) (a.apart.sub_right (Region.sub_prefix (by decide)))) fun v ⟨valid,frame,g,q⟩ => ?_
  have sv : SavedAt v.mem w o := by
    apply (k.mem ▸ a.saved).frame frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact a.apart.symm.sub_left (Offset.sub_base _ (by decide))
  refine WP.mono (restore_ok ((g _ (by decide)).trans workReg) a.workAlign
    (by rw [q.rd,q.wr]; exact work) sv (q.sp.trans (k.sp.trans a.sp))) fun t ⟨ret,mem,_,rd,wr⟩ => ?_
  rw [mem,k.mem] at *
  exact ⟨ret,valid,frame,rd.trans (q.rd.trans k.rd),wr.trans (q.wr.trans k.wr)⟩

theorem exit_rel {s t o p : State} (a : ExitArgs s o w tag) (b : ExitArgs t p w tag)
    (sp : s.sp = t.sp) : RelCT isa (Eq2 s t) (.block exitCode) TT := by
  rw [exitCode,List.append_assoc]
  apply RelCT.block_append
  refine rel_seq (rel_taint [] sp (by simp) (by taint_decide)) (load_wp a) (load_wp b)
    fun _ _ ⟨ta,wa,ka⟩ ⟨tb,wb,kb⟩ => ?_
  refine rel_taint [.s9,.s0] (ka.sp.trans (sp.trans kb.sp.symm)) ?_ (by taint_decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ta.trans tb.symm
  · exact wa.trans wb.symm

end VG.Proof.AesGcm.RISCV64.Contiguous
