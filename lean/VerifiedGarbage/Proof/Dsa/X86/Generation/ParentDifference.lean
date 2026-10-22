module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentConstants
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryMinusOne
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Reuse modulus subtraction under the caller's full generation permissions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem parent_difference_at {s : State} {base : Addr} {bytes n candidate r out input : Nat}
    (scr : Scr s base bytes) (capacity : montgomeryBytes ≤ bytes)
    (C : ParentContext base n candidate s) (positive : 0 < n)
    (ho : out < 9) (hi : input < 9) (ho0 : out ≠ 0) (hoi : out ≠ input)
    (value : val32 s.mem base (slot n input) (2 * n) = r) (reduced : r < candidate) :
    WP isa (parentDifference n out input) s fun t =>
      ParentContext base n candidate t ∧ val32 t.mem base (slot n out) (2 * n) = candidate - r ∧
      Outside base (slot n out) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have write := workspace_prefix_covers scr capacity
  refine WP.mono (workspace_wp (parent_difference C positive ho hi ho0 hoi value reduced)
    (Covers.append (Covers.refl _) write) write)
    fun t ⟨u, ⟨_, result, F, K⟩, eq⟩ => ?_
  subst eq
  have physicalK : Keeps [.eax, .ecx, .edx, .ebp] s (u.withRegions s.rd s.wr) := ⟨K.1, rfl, rfl⟩
  have below := slot_le (n := n) (i := 0) (j := out) (by omega)
  refine ⟨C.outside_keep physicalK (by decide) (by decide) F
    (.inl (by unfold stride at below; omega)) (by have := slot_header n out; omega),
    result, F, physicalK⟩

end VG.Proof.Dsa.X86.Generation
