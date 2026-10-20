module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeState
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeState

/-! # Tape cursor operations read only public frame words -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem chunkCheck_check (slots : TapeSlots) (width : Nat)
    (kind : slots = seedTape ∨ slots = generatorTape) :
    (taint.check (τr [.esp]) (.block (chunkCheck slots width)) (.block [])).isSome = true := by
  rcases kind with rfl | rfl
  all_goals exact (congrArg Option.isSome (check_of_erase_eq _ (.block (chunkCheck _ 1)) (τr [.esp])
    (.block []) rfl rfl rfl)).trans (by rfl)

theorem tapeTake_check (slots : TapeSlots) (width : Nat)
    (kind : slots = seedTape ∨ slots = generatorTape) :
    (taint.check (τr [.esp]) (.block (tapeTake slots width)) (.block [])).isSome = true := by
  rcases kind with rfl | rfl
  all_goals exact (congrArg Option.isSome (check_of_erase_eq _ (.block (tapeTake _ 1)) (τr [.esp])
    (.block []) rfl rfl rfl)).trans (by rfl)

theorem tapeReset_check (slots : TapeSlots) (kind : slots = seedTape ∨ slots = generatorTape) :
    (taint.check (τr [.esp]) (.block (tapeReset slots)) (.block [])).isSome = true := by
  rcases kind with rfl | rfl <;> taint_decide

structure TapeCheckPublic where
  frame : PublicFrame
  used : Nat
  total : Nat

def TapeCheckAt (slots : TapeSlots) (p : TapeCheckPublic) (s : State) : Prop :=
  FrameAt [slots.used, slots.total] p.frame s ∧ p.used ≤ p.total ∧ p.total < 2 ^ 32 ∧
    p.frame.words slots.used = BitVec.ofNat 32 p.used ∧ p.frame.words slots.total = BitVec.ofNat 32 p.total

theorem chunkCheck_ct (slots : TapeSlots) (width : Nat) (hu : slots.used < 37) (ht : slots.total < 37)
    (hw : width < 2 ^ 32) (kind : slots = seedTape ∨ slots = generatorTape) : RelCT isa (Two (TapeCheckAt slots)) (.block (chunkCheck slots width))
    (Two fun p s => TapeCheckAt slots p s ∧ s.cf = some (decide (p.total - p.used < width))) := by
  refine two_piece [.esp] (fun p s t hs ht => frameAt_pins _ p.frame s t hs.1 ht.1)
    (chunkCheck_check slots width kind) ?_
  rintro p s ⟨F, hle, htotal, used, total⟩
  refine WP.mono (chunkCheck_ok F.1 (observedWords_rep p.frame.base s) slots hu ht hle htotal hw
    ((F.2 _ (by simp)).trans used) ((F.2 _ (by simp)).trans total)) fun t ⟨cf, mem, K⟩ => ?_
  exact ⟨⟨F.keep mem K (by decide), hle, htotal, used, total⟩, cf⟩

theorem tapeStatus_ct : RelCT isa (Two (FrameAt [19])) (.block tapeStatus)
    (Two fun (p : PublicFrame) s => s.zf = some (p.words 19 == 3)) := by
  refine two_piece [.esp] (frameAt_pins _) (by taint_decide) ?_
  intro p s R
  refine WP.mono (tapeStatus_ok R.1 (observedWords_rep p.base s)) fun t ⟨zf, _, _⟩ => ?_
  rw [zf]
  change some (s.mem.readW (off p.base 76) 32 == 3) = _
  rw [R.2 19 (by simp)]
end VG.Proof.Dsa.X86.Generation
