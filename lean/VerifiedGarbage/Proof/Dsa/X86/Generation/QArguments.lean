module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Public digest and candidate pointers for the shared subgroup shaper. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

theorem q_arguments {s : State} {scratch : BitVec 32} {digestOffset candidateOffset len : Nat}
    (pointer : s.gpr .ebp = scratch) :
    WP isa (.block (qArguments digestOffset candidateOffset len)) s fun t =>
      t.gpr .esi = scratch + BitVec.ofNat 32 digestOffset ∧
      t.gpr .ebx = scratch + BitVec.ofNat 32 candidateOffset ∧
      t.gpr .ecx = BitVec.ofNat 32 len ∧ t.mem = s.mem ∧ Keeps [.esi, .ebx, .ecx] s t := by
  unfold qArguments
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ =>
    wp_movS rfl fun c C _ => wp_addS rfl fun d D _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, T.gpr, ?_, ?_⟩
  · rw [T.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.gpr, pointer]
  · rw [T.other .ebx (by decide), D.gpr, C.gpr, B.other .ebp (by decide), A.other .ebp (by decide), pointer]
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
  · exact (((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide)))).trans (T.keeps.mono (by decide))

end VG.Proof.Dsa.X86.Generation
