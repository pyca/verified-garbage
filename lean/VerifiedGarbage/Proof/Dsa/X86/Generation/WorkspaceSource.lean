module

public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Select a public byte buffer within the existing workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem workspace_source {s : State} (d : Nat) :
    WP isa (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 d))]) s fun t =>
      t.gpr .esi = s.gpr .edi + BitVec.ofNat 32 d ∧ t.mem = s.mem ∧ Keeps [.esi] s t := by
  refine wp_movS rfl fun a A _ => wp_addS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.gpr, A.gpr], T.mem.trans A.mem, A.keeps.trans T.keeps⟩

end VG.Proof.Dsa.X86.Generation
