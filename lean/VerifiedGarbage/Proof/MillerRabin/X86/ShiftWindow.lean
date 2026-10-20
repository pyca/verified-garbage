module

public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Four native-word doublings advance one fixed-width secret window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem doubleFour_ok (s : State) :
    WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)]) s fun t =>
      t.gpr .eax = s.gpr .eax <<< 4 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b B _ =>
    wp_addS rfl fun c C _ => wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (C.mem.trans (B.mem.trans A.mem)),
    ((A.keeps.trans B.keeps).trans C.keeps).trans T.keeps⟩
  rw [T.gpr, C.gpr, B.gpr, A.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

end VG.Proof.MillerRabin.X86
