module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Mont.X86
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry

/-! # Arena clearing addresses and loop counts are public -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem clearScratch_ct (plen : Nat) : RelCT isa (Two (FrameAt [5])) (clearScratch plen) (fun _ _ => True) := by
  unfold clearScratch
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .esi = p.words 5 ∧
    s.gpr .ecx = BitVec.ofNat 32 (usedBytes plen)) [.esp] (frameAt_pins _) (hc := .block []) ?_ ?_) ?_
  · exact (congrArg Option.isSome (Dynamic.check_of_erase_eq _
      (.block [.mov .esi (.mem (frameSlot 5)), .mov .ecx (.imm 0), .mov .eax (.imm 0)])
      (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro p s R
    refine wp_movS (by rw [R.1.readSlot (by decide : 5 < 37), R.2 5 (by simp)]) fun a sa _ =>
      wp_movS rfl fun b ab _ => wp_movS rfl fun t bt _ => WP.block_nil ?_
    exact ⟨(bt.other _ (by decide)).trans ((ab.other _ (by decide)).trans sa.gpr),
      (bt.other _ (by decide)).trans ab.gpr⟩
  · refine two_taint [.esi, .ecx] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hs.1.trans ht.1.symm, hs.2.trans ht.2.symm]
end VG.Proof.Dsa.X86.Generation
