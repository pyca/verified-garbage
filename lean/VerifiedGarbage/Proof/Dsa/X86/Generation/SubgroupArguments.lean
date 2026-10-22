module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashRegisters

/-! Set up the public hash workspace without changing the seed pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

theorem subgroup_arguments {s : State} {base : BitVec 32} {seedLen : Nat}
    (pointer : s.gpr .edi = base) :
    WP isa (.block (subgroupArguments seedLen)) s fun t =>
      HashRegisters (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash) (s.gpr .esi)
        (base + BitVec.ofNat 32 subgroupHashScratch) seedLen t ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edi] s t := by
  unfold subgroupArguments
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ =>
    wp_movS rfl fun c C _ => wp_addS rfl fun d D _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ebp, .edi] s t :=
    (((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans
      ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide)))).trans (T.keeps.mono (by decide))
  refine ⟨⟨?_, K.1 .esi (by decide), T.gpr, ?_⟩, ?_, K⟩
  · rw [T.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), B.gpr, A.gpr, pointer]
  · rw [T.other .ebp (by decide), D.gpr, C.gpr, B.other .edi (by decide), A.other .edi (by decide), pointer]
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.Dsa.X86.Generation
