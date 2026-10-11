import VerifiedGarbage.Proof.Sm3.X86_64.Compress
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Sm3.X86_64.Stream

/-!
# Streaming SM3 on x86-64: `init`
-/

namespace VG.Proof.Sm3.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sm3.X86_64.Stream
open VG.Impl.Sm3.X86_64 (at_)
open VG.Proof.Sm3.X86_64 (ea_at contains_offset' writeState stateAt_writeState)

/-! ## `init` -/

theorem init_eq : init = .block [
    .mov32 .rax (.imm 0x7380166f), .store32 (at_ .rdi (4 * 0)) .rax,
    .mov32 .rax (.imm 0x4914b2b9), .store32 (at_ .rdi (4 * 1)) .rax,
    .mov32 .rax (.imm 0x172442d7), .store32 (at_ .rdi (4 * 2)) .rax,
    .mov32 .rax (.imm 0xda8a0600), .store32 (at_ .rdi (4 * 3)) .rax,
    .mov32 .rax (.imm 0xa96f30bc), .store32 (at_ .rdi (4 * 4)) .rax,
    .mov32 .rax (.imm 0x163138aa), .store32 (at_ .rdi (4 * 5)) .rax,
    .mov32 .rax (.imm 0xe38dee4d), .store32 (at_ .rdi (4 * 6)) .rax,
    .mov32 .rax (.imm 0xb0fb0e4e), .store32 (at_ .rdi (4 * 7)) .rax] := rfl

theorem init_post {s₀ : State}
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 96⟩) (g : Reg → BitVec 64)
    (hg : ∀ r, r ≠ .rax → g r = s₀.gpr r) :
    gprPreserved s₀ { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Sm3.iv } ∧
      Proof.Sm3.initX86_64.post s₀
        { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Sm3.iv } := by
  have hf : Frame [⟨s₀.gpr .rdi, 96⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) Spec.Sm3.iv) := by
    have c : ∀ k, k < 8 → (⟨s₀.gpr .rdi, 96⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
      fun k hk => contains_offset' (by omega) (by omega)
    simp only [writeState]
    refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
      (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, Stream.repr_nil (stateAt_writeState _ _ _)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)

set_option simprocs false in
theorem init_correct {s₀ : State} (hp : Proof.Sm3.initX86_64.pre s₀) :
    WP isa init s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sm3.initX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .rdi, 96⟩, by simp [hwr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 0 (by omega); have o1 := o 1 (by omega); have o2 := o 2 (by omega)
  have o3 := o 3 (by omega); have o4 := o 4 (by omega); have o5 := o 5 (by omega)
  have o6 := o 6 (by omega); have o7 := o 7 (by omega)
  rw [init_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.store32,
    State.setReg32, State.setReg, o0, o1, o2, o3, o4, o5, o6, o7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact init_post hret _ fun r hr => by simp [hr]

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

theorem init_verified : Verified X86_64.target init Proof.Sm3.initX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sm3.X86_64.Stream
