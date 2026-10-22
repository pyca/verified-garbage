module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Seed addition scans a fixed number of public addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

private theorem byte_checked (i : Nat) : VG.Taint.check taint (τr [.esi, .ebx])
    (.block (seedAddByte i)) (.block []) = some (τr [.esi, .ebx]) := by kernel_rfl

theorem seed_add_byte_ct (i : Nat) :
    RelCT isa (fun s t => s.gpr .esi = t.gpr .esi ∧ s.gpr .ebx = t.gpr .ebx) (.block (seedAddByte i))
      (fun s t => s.gpr .esi = t.gpr .esi ∧ s.gpr .ebx = t.gpr .ebx) := by
  intro s t tr ur s' t' ⟨source, dest⟩ E F
  have A : VG.X86.Taint.Agree (τr [.esi, .ebx]) s t := by
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact source
    · exact dest
  obtain ⟨trace, after⟩ := VG.Taint.check_sound (byte_checked i) A E F
  exact ⟨trace, after.rf.1 .esi (by decide), after.rf.1 .ebx (by decide)⟩

theorem seed_add_ct (n : Nat) :
    RelCT isa (fun s t => s.gpr .esi = t.gpr .esi ∧ s.gpr .ebx = t.gpr .ebx) (seedAdd n)
      (fun s t => s.gpr .esi = t.gpr .esi ∧ s.gpr .ebx = t.gpr .ebx) := by
  induction n with
  | zero => exact RelCT.nil (fun _ _ h => h)
  | succ n ih => exact (seed_add_byte_ct n).seq ih

end VG.Proof.Dsa.X86.Generation
