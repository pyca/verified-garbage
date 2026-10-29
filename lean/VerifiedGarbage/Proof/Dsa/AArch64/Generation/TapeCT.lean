module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Tape bookkeeping accesses only public stack addresses -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem tapeReset_ct {α : Type} {Φ : α → State → Prop} (slots : TapeSlots)
    (hs : slots = seedTape ∨ slots = generatorTape) :
    RelCT isa (Two Φ) (.block (tapeReset slots)) (fun _ _ => True) := by
  rcases hs with rfl | rfl
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem chunkCheck_ct {α : Type} {Φ : α → State → Prop} (slots : TapeSlots) (width : Nat)
    (hs : slots = seedTape ∨ slots = generatorTape)
    (hw : width = 20 ∨ width = 32 ∨ width = 128 ∨ width = 256 ∨ width = 384) :
    RelCT isa (Two Φ) (.block (chunkCheck slots width)) (fun _ _ => True) := by
  rcases hs with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem tapeTake_ct {α : Type} {Φ : α → State → Prop} (slots : TapeSlots) (width : Nat)
    (hs : slots = seedTape ∨ slots = generatorTape)
    (hw : width = 20 ∨ width = 32 ∨ width = 128 ∨ width = 256 ∨ width = 384) :
    RelCT isa (Two Φ) (.block (tapeTake slots width)) (fun _ _ => True) := by
  rcases hs with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
