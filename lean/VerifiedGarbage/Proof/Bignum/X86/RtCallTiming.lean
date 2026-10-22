module

public import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul

/-! Timing of a shared Montgomery call once its public arguments are ready. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.RtCall
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (calleeOf rtPub_of calleeOf_eq rtPre_of)

structure CallState (base : Addr) (bytes : Nat) (sp : BitVec 32)
    (values : Nat → BitVec 32) (g : State) : Prop where
  abi : RtABI (calleeOf g base bytes)
  stack : g.gpr .esp = sp - BitVec.ofNat 32 36
  args : ∀ i < 9, arg (calleeOf g base bytes) i = values i
  frame : (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr
  workspace : (⟨base, bytes⟩ : Region) ∈ g.wr

theorem call_ct {base : Addr} {bytes : Nat} {sp : BitVec 32} {values : Nat → BitVec 32} :
    RelCT isa (fun s t => CallState base bytes sp values s ∧ CallState base bytes sp values t)
      (.call Spec.Rsa.MontMul.mulApi.name VG.Impl.Mont.X86.Rt.body) (fun _ _ => True) := by
  refine RelCT.call (k := Spec.Rsa.MontMul.mulContract abi 0) rt_correct rt_constantTime
    [⟨(sp - BitVec.ofNat 32 36).setWidth 64, 36⟩] [⟨base, bytes⟩] ?_
  rintro g₁ g₂ ⟨h₁, h₂⟩
  have c₁ := calleeOf_eq (base := base) (bytes := bytes) h₁.stack
  have c₂ := calleeOf_eq (base := base) (bytes := bytes) h₂.stack
  have fr₁ := h₁.frame
  have fr₂ := h₂.frame
  rw [h₁.stack] at fr₁
  rw [h₂.stack] at fr₂
  refine ⟨c₁ ▸ rtPre_of h₁.abi, c₂ ▸ rtPre_of h₂.abi, ?_, Covers.of_mem fun r hr => ?_,
    Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_,
    by rw [h₁.stack, h₂.stack]⟩
  · rw [← c₁, ← c₂]
    refine rtPub_of ?_ fun i hi => (h₁.args i hi).trans (h₂.args i hi).symm
    simp only [VG.Proof.Bignum.X86.PublicRt.calleeOf, State.withRegions_gpr, State.callEntry_esp,
      h₁.stack, h₂.stack]
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · exact List.mem_append_right _ fr₁
    · exact List.mem_append_right _ h₁.workspace
  · rw [List.mem_singleton.mp hr]
    exact h₁.workspace
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · exact List.mem_append_right _ fr₂
    · exact List.mem_append_right _ h₂.workspace
  · rw [List.mem_singleton.mp hr]
    exact h₂.workspace

end VG.Proof.Bignum.X86.RtCall
