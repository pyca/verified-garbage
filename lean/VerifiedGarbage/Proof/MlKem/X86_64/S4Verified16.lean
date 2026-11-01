module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall

/-!
# ML-KEM on x86-64: `vg_mlkem16_sample_ntt4`, verified

The code of `vg_mlkem_sample_ntt4_avx2` and `_avx512` with 16-bit stores
(`w16 := true`), whose proofs are theirs for either width (`S4.correct`,
`S4.ct`); `sample4KW true` implies the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample4_16Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 136⟩]
  wr := [⟨0x2000, 2048⟩, ⟨0x4000, 8192⟩]

theorem pBytes_true : Impl.MlKem.X86_64.Sample4.pBytes true = 512 := rfl

theorem sample4_16_post {s s' : State} (h : (sample4KW true).post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Proof.MlKem.ReducedW 16 s'.mem (Proof.MlKem.poly4_16 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ iters, Spec.MlKem.sampleNTT iters (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) =
          some (Proof.MlKem.polyAtW 16 s'.mem (Proof.MlKem.poly4_16 (s.gpr .rsi) k))) ∨
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
      exact ⟨Spec.MlKem.minIterations, by rw [e]; exact congrArg some (hp k hk f e).2.symm⟩
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, Option.not_isSome_iff_eq_none.mp hk'⟩

theorem sample4_16_of_correct {c : Prog isa}
    (hok : ∀ σ, (sample4KW true).pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ (sample4KW true).post σ s')
    (hct : ConstantTime isa (sample4KW true).pre (sample4KW true).pub c) :
    Verified X86_64.target c (Proof.MlKem.sampleNTT4_16Contract X86_64.abi 24) :=
  Verified.of_correct hok hct
    { pre := by sig_implies_pre [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW,
        pBytes_true, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW, X86_64.abi, X86_64.argRegs]
        exact sample4_16_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW, X86_64.abi,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW, X86_64.abi,
          X86_64.argRegs]
        sig_simp [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW, X86_64.abi,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact map_toNat_inj ‹_›
      sat := by
        sig_implies_sat [Proof.MlKem.sampleNTT4_16Contract, Proof.MlKem.sampleNTT4_16Sig, sample4KW,
          pBytes_true, X86_64.abi, X86_64.argRegs] [sample4_16Sat] using sample4_16Sat }

/-- `vg_mlkem16_sample_ntt4_avx2` and `vg_mlkem16_sample_ntt4_avx512`. -/
theorem sample4_16_verified {fast : Bool} : Verified X86_64.target
    (Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 fast true) (Proof.MlKem.sampleNTT4_16Contract X86_64.abi 24) :=
  sample4_16_of_correct (S4.correct (w16 := true) (fast := fast)) (S4.ct (w16 := true) (fast := fast))

end VG.Proof.MlKem.X86_64
