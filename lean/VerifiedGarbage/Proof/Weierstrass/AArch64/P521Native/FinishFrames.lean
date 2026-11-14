module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldProgram
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! Exact write-set adapter for finite ordinary-field programs. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Mont.AArch64.P521Field

def fieldProgramWrites (loc : Nat → Nat) (ops : List PointOp) : List (Nat × Nat) :=
  ops.map (fun op => (loc op.out,72))++[(3952,72)]

theorem field_program_frame_unch {base : Addr} {loc : Nat → Nat} {ops : List PointOp} {m m' : Mem}
    (h : FieldProgramFrame base loc ops m m') : Unch base (fieldProgramWrites loc ops) m m' := by
  intro x hx
  refine h x ?_ ?_
  · intro op hop
    exact hx (loc op.out,72) (List.mem_append_left _ (List.mem_map.mpr ⟨op,hop,rfl⟩))
  · exact hx (3952,72) (List.mem_append_right _ (List.mem_singleton.mpr rfl))

end VG.Proof.Weierstrass.AArch64.P521Native
