module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTableCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ClearScratchCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.InitializeSearch
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStorage
import VerifiedGarbage.Proof.Dsa.X86.Generation.ClearScratch
import VerifiedGarbage.Proof.Dsa.X86.Generation.ClearScratchCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTableCT

/-! # Public arena geometry determines the one-time search initialization trace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

def StorageAt (plen : Nat) (P : SearchContextPlan) (s : State) : Prop :=
  (∃ W, SearchStorage P W s ∧ W 16 = 0) ∧ P.geometry.pLen = plen

theorem storageAt_frame {plen : Nat} {P : SearchContextPlan} {s : State} (R : StorageAt plen P s) :
    FrameAt [5] ⟨P.geometry.frameBase, P.saved⟩ s := by
  obtain ⟨⟨W, R, _⟩, _⟩ := R
  exact ⟨R.arena.frame, fun i hi => by obtain rfl := List.mem_singleton.mp hi; exact
    (R.representation 5 (by decide)).trans (R.fixed 5 (by decide) (by decide))⟩

theorem initializeSearch_ct (plen : Nat) : RelCT isa (Two (StorageAt plen)) (initializeSearch plen) (fun _ _ => True) := by
  unfold initializeSearch
  refine RelCT.seq (two_post (Ψ := StorageAt plen)
    (two_map (fun P => ⟨P.geometry.frameBase, P.saved⟩) (fun _ _ h => storageAt_frame h) (clearScratch_ct plen)) ?_)
    (RelCT.seq (two_piece (Ψ := fun P s => Scr s P.geometry.base 8192) [.esp] ?_ (by taint_decide) ?_)
      (two_map (fun P => P.geometry.base) (fun _ _ h => h) ((trialTable_ct 1024 (Nat.le_refl _)).mono (fun _ _ h => h) (fun _ _ _ => trivial))))
  · rintro P s ⟨⟨W, R, cursor⟩, width⟩
    have parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
    refine WP.mono (clearScratch_ok R.arena.frame R.representation
      (by have := P.geometry.width; unfold usedBytes domainCheck; omega)
      (by rw [parent, ← width]; exact P.geometry.arenaBound)
      (by intro i hi; rw [parent]; apply R.arena.write; rw [width]; omega)) fun t ⟨O, _, K⟩ => ?_
    rw [parent, ← width] at O
    exact ⟨⟨W, R.keep O K (by decide), cursor⟩, width⟩
  · intro P s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact frameAt_pins [5] _ s t (storageAt_frame hs) (storageAt_frame ht) .esp (by decide)
  · rintro P s ⟨⟨W, R, _⟩, _⟩
    have parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
    refine wp_movS (R.arena.frame.readWord R.representation (by decide : 5 < 37)) fun t st _ => WP.block_nil ?_
    refine ⟨by rw [st.gpr, parent]; rfl, by rw [st.wr]; exact R.tableWrite, ?_, ?_⟩
    · rw [P.geometry.base_toNat]
      have := P.geometry.arenaBound
      unfold usedBytes domainCheck at this
      omega
    · rw [st.other _ (by decide), R.arena.frameReg]
      have h := P.geometry.part_stk (d := 0) (n := 8192)
        (by unfold usedBytes domainCheck; omega) (by unfold usedBytes domainCheck; omega)
      simpa only [off, BitVec.add_zero] using h
end VG.Proof.Dsa.X86.Generation
