module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Entry
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
meta import VerifiedGarbage.Proof.Framework.RISCV64.ResidueTaintSound
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Timing and residue of contiguous RISC-V seal -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

theorem entry_rel {s t : State} (a : EntryArgs s w tag) (b : EntryArgs t w tag')
    (sp : s.sp = t.sp) : RelCT isa (Eq2 s t) (.block entry) TT := by
  unfold entry
  rw [oneEntryAt_eq,List.append_assoc]
  apply RelCT.block_append
  refine rel_seq (rel_taint [] sp (by simp) (by taint_decide))
    (oneAg_ok (off := 24) (by decide) a.spAlign (a.slot 3 (by decide)) a.scratch)
    (oneAg_ok (off := 24) (by decide) b.spAlign (b.slot 3 (by decide)) b.scratch)
    fun x y ⟨u,_,ku⟩ ⟨v,_,kv⟩ => ?_
  refine rel_taint [.t1] (ku.sp.trans (sp.trans kv.sp.symm)) ?_ (by taint_decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact u.trans v.symm

theorem payloadArgs_rel {s t : State} (sp : s.sp = t.sp) (work : s.gpr .s0 = t.gpr .s0) :
    RelCT isa (Eq2 s t) (.block payloadArgs) TT := by
  refine rel_taint [.s0] sp ?_ (by taint_decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact work

/-- All saved bytes, register spills and temporaries are public after the scrub. -/
theorem residue : ∃ hc, (rtaint.check (RTaint.init 4656 []) code hc).any (RTaint.done 0) = true :=
  ⟨_, by taint_decide_ct⟩

end VG.Proof.AesGcm.RISCV64.Contiguous
