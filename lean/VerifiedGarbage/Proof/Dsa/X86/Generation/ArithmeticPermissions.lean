module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticFrame
import VerifiedGarbage.Proof.Framework.Covers

/-! Drop writable argument-frame permissions while the arithmetic runs. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem ArithmeticSetup.permissions {s t : State} {base : Addr} {bytes : Nat}
    (H : ArithmeticSetup s t) (workspace : (⟨base, bytes⟩ : Region) ∈ t.wr) :
    Covers (arithmeticRead t ++ [⟨base, bytes⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨base, bytes⟩] t.wr := by
  have frame : (⟨(t.gpr .esp).setWidth 64, 16⟩ : Region) ∈ t.wr := by
    rw [H.keeps.1 .esp (by decide), H.keeps.2.2, allocFrame_wr]
    exact List.mem_cons_self ..
  refine ⟨Covers.of_mem ?_, Covers.of_mem ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_append_right _ frame
      · exact List.mem_append_left _ hr
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ workspace
  · intro r hr
    rw [List.mem_singleton.mp hr]; exact workspace

end VG.Proof.Dsa.X86.Generation
