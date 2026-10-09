import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourGroups_ok (body : Nat → List Instr) (I : Nat → State → Prop) {s : State}
    (h : I 0 s)
    (step : ∀ i<4,∀t,I i t → WP isa (.block (body (16*i))) t (I (i+1))) :
    WP isa (.block ([0,16,32,48].flatMap body)) s (I 4) := by
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (step 0 (by decide) s h) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (step 1 (by decide) a ha) fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (step 2 (by decide) b hb) fun c hc => ?_
  exact step 3 (by decide) c hc

def advance (ptrs : List Reg) : List Instr :=
  ptrs.map (fun r => .addImm .x r r 64) ++ [.subImm .x .x10 .x10 1]

theorem advance2_ok (s : State) : WP isa (.block (advance [.x0,.x1])) s fun t =>
    ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x10=s.gpr .x10-1 ∧
      t.mem=s.mem) ∧ Keep [.x0,.x1,.x10] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  arun [List.map_cons,List.map_nil,List.cons_append,List.nil_append]
  exact ⟨rfl,rfl,rfl⟩

theorem advance3_ok (s : State) : WP isa (.block (advance [.x0,.x1,.x2])) s fun t =>
    ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x2=s.gpr .x2+64 ∧
      t.gpr .x10=s.gpr .x10-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x1,.x2,.x10] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  arun [List.map_cons,List.map_nil,List.cons_append,List.nil_append]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem counter_ok (s : State) : WP isa (.block [.movz .x .x10 16 0]) s fun t =>
    ((t.gpr .x10=16 ∧ t.mem=s.mem) ∧ Keep [.x10] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun

end VG.Proof.MlDsa.AArch64.Optimized.Response
