module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStorage
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
import VerifiedGarbage.Proof.Dsa.X86.Generation.ClearScratch

/-! # Clear the arena and initialize the divisor table once per generation call -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem initializeSearch_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchStorage P W s) :
    WP isa (.seq (clearScratch P.geometry.pLen)
      (.seq (.block [.mov .edi (.mem (frameSlot 5))]) (trialTable 1024))) s fun t =>
        SearchContext P W t ∧ Frame [⟨P.geometry.base, usedBytes P.geometry.pLen⟩] s.mem t.mem ∧
        Keeps [.eax, .ecx, .esi, .edi] s t := by
  have parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have size : usedBytes P.geometry.pLen < 2 ^ 32 := by have := P.geometry.width; unfold usedBytes domainCheck; omega
  refine WP.seq (WP.mono (clearScratch_ok R.arena.frame R.representation size
    (by rw [parent]; exact P.geometry.arenaBound)
    (by intro i hi; rw [parent]; exact R.arena.write (by omega))) fun a ⟨Oa, _, Ka⟩ => ?_)
  rw [parent] at Oa
  have Ra := R.keep Oa Ka (by decide)
  refine WP.seq (wp_movS (Ra.arena.frame.readWord Ra.representation (by decide : 5 < 37)) fun b ab _ => WP.block_nil ?_)
  have Ob : Frame [⟨P.geometry.base, usedBytes P.geometry.pLen⟩] a.mem b.mem := by rw [ab.mem]; exact Frame.refl _ _
  have Rb := Ra.keep Ob ab.keeps (by decide)
  have scr : Scr b P.geometry.base 8192 := by
    refine ⟨by rw [ab.gpr, parent]; rfl, Rb.tableWrite, ?_, ?_⟩
    · rw [P.geometry.base_toNat]
      have := P.geometry.arenaBound
      unfold usedBytes domainCheck at this
      omega
    · rw [Rb.arena.frameReg]
      have h := P.geometry.part_stk (d := 0) (n := 8192)
        (by unfold usedBytes domainCheck; omega) (by unfold usedBytes domainCheck; omega)
      simpa only [off, BitVec.add_zero] using h
  refine WP.mono (trialTable_ok scr 1024 (Nat.le_refl _)) fun t ⟨table, Ot, Kt⟩ => ?_
  have Ot' : Frame [⟨P.geometry.base, usedBytes P.geometry.pLen⟩] b.mem t.mem := Ot.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simpa only [off, BitVec.add_zero] using (Offset.sub_base P.geometry.base
      (d := 0) (n := 8192) (k := usedBytes P.geometry.pLen) (by unfold usedBytes domainCheck; omega)))
  exact ⟨(Rb.keep Ot' Kt (by decide)).context table, Oa.trans (Ob.trans Ot'),
    (Ka.mono (by decide)).trans ((ab.keeps.mono (by decide)).trans (Kt.mono (by decide)))⟩
end VG.Proof.Dsa.X86.Generation
