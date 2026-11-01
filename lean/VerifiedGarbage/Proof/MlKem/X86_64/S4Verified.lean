module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base


/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`'s contract

What the proofs of `vg_mlkem_sample_ntt4` share in showing that the contract
they are written against (`sample4K`) implies the shared one of `Spec/`: its
postcondition (`sample4_post`), and a state it permits (`sample4Sat`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 136⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem sample4_post {s s' : State} (h : sample4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Proof.MlKem.Reduced s'.mem (Proof.MlKem.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ iters, Spec.MlKem.sampleNTT iters (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) =
          some (Proof.MlKem.polyAt s'.mem (Proof.MlKem.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
          (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  by_cases hall : ((List.range 4).all fun k =>
      (Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k)).isSome) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, ∃ f, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
        (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) = some f := fun k hk => by
      have := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
      exact Option.isSome_iff_exists.mp this
    refine ⟨fun _ k hk => ?_, .inl ⟨hr, fun k hk => ?_⟩⟩
    · obtain ⟨f, e⟩ := hs k hk; exact (hp k hk f e).1
    · obtain ⟨f, e⟩ := hs k hk
      exact ⟨Spec.MlKem.minIterations, by rw [e, (hp k hk f e).2]⟩
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, Option.not_isSome_iff_eq_none.mp hk'⟩

end VG.Proof.MlKem.X86_64
