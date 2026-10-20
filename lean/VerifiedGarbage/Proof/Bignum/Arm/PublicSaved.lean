module
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.TCB.Arm.Isa

/-! # The secret acceptance slot does not overlap saved AAPCS registers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem public_callee_saved {s t : State} {base dst : BitVec 32} {len k : Nat} {g : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) g pcCalleeSaved)
    (frame : Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem)
    (workspace : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr base, 8 * len⟩)
    (output : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr dst, k⟩) :
    Spill.Saved t.mem (State.addr s.sp) g pcCalleeSaved := by
  intro p hp
  have fit : p.2 + 4 ≤ 56 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have gap : p.2 + 4 ≤ 48 ∨ 52 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sub : (⟨off (State.addr s.sp) p.2, 4⟩ : Region).Sub ⟨State.addr s.sp, 56⟩ :=
    Offset.sub_base _ fit
  have keep := frame.readW (a := off (State.addr s.sp) p.2) (w := 32) (r := ⟨off (State.addr s.sp) p.2, 4⟩) (by simp [Region.Contains])
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact workspace.sub_left sub
      · exact Offset.disjoint _ gap (by omega) (by decide)
      · exact output.sub_left sub) (by decide : 32 / 8 < 2 ^ 64)
  exact keep.trans (saved p hp)

end VG.Proof.Bignum.Arm
