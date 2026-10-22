module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeContext
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Preparation touches only the parent, arithmetic subspace and outgoing stack. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

def PreparationFrame (base : Addr) (sp : BitVec 32) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩,
    below sp 40] s.mem t.mem

theorem preparation_parent_frame {base : Addr} {sp : BitVec 32} {s t : State}
    (F : Frame [⟨base, montgomeryBytes⟩] s.mem t.mem) : PreparationFrame base sp s t :=
  F.sub (by intro r hr; rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, fun _ h => h⟩)

theorem preparation_arithmetic_frame {base : Addr} {sp : BitVec 32} {size : Nat} {s t : State}
    (F : Frame [⟨off base Layout.arithmetic, size⟩] s.mem t.mem) (bound : size ≤ Layout.arithmeticBytes) :
    PreparationFrame base sp s t :=
  F.sub (by intro r hr; rw [List.mem_singleton.mp hr]
            exact ⟨_, by simp, Region.sub_prefix bound⟩)

theorem parent_arithmetic_apart (base : Addr) {size : Nat} (bound : size ≤ Layout.arithmeticBytes) :
    Region.Disjoint ⟨base, montgomeryBytes⟩ ⟨off base Layout.arithmetic, size⟩ :=
  (Offset.disjoint_base base (by decide : montgomeryBytes ≤ Layout.arithmetic)
    (by unfold Layout.arithmetic Layout.arithmeticBytes at *; omega)).symm

theorem parent_stack_apart {base : Addr} {sp : BitVec 32} {bytes : Nat}
    (room : CallRoom sp base bytes) (capacity : montgomeryBytes ≤ bytes) :
    Region.Disjoint ⟨base, montgomeryBytes⟩ (below sp 16) :=
  ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right (Region.sub_prefix capacity)).symm

theorem preparation_montgomery_frame {base : Addr} {sp : BitVec 32} {n : Nat} {s t : State}
    (F : MontgomerySetupFrame base sp n s t) (upper : n ≤ 48) : PreparationFrame base sp s t := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Region.sub_prefix (by
      simp only [contextBytes, slot, stride, montgomeryBytes]; omega)⟩
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base (by
      simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes, montgomeryBytes]; omega)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem preparation_factor_frame {base : Addr} {sp : BitVec 32} {s t : State}
    (F : Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, below sp 16] s.mem t.mem)
    (low : 40 ≤ sp.toNat) : PreparationFrame base sp s t := by
  apply F.sub
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, below_sub (by decide) low⟩

theorem preparation_candidate_frame {base : Addr} {sp : BitVec 32} {s t : State} {n : Nat}
    (F : Outside base (Layout.arithmetic + 160) (8 * n) s.mem t.mem) (upper : n ≤ 48) :
    PreparationFrame base sp s t := by
  have frame := F.frameAt (by unfold Layout.arithmetic; omega)
  apply frame.sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, by simp,
    Offset.sub base (by omega) (by unfold Layout.arithmeticBytes; omega)⟩

end VG.Proof.Dsa.X86.Generation
