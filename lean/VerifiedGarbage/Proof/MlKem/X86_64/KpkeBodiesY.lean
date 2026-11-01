module
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract

import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR101
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.FinY
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100

/-!
# ML-KEM on x86-64: the AVX2 arithmetic without its MXCSR region

As `KpkeBodies.lean` and `KpkeAcc.lean`, for `Bodies.avx2`:
`vg_mlkem_ntt_avx2`'s code storing through `r10` (`nttOBY`), without
`withMxcsr`, meets the contract of the function (the proof is that of
`NttAvx2.lean` without `withMxcsr_ok`), and the pieces around the
accumulator in words (`AccY.lean`, `AccInvY.lean`, `FinY.lean`) meet theirs.
The same code reading its input as `u16`s (`nttR16`) meets `nttO16K`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `mov rdi, r10`, keeping both lanes of the vector registers. -/
theorem movDiR10Y_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .r10)]) s fun s' => s'.gpr .rdi = s.gpr .r10 ∧ s'.mem = s.mem ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧ Keep [.rdi] s s' := by
  vrunm [lane_setReg]
  refine ⟨fun _ _ => trivial, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem nttOBY_correct (s : State) (hs : nttOK.pre s) :
    ∃ t s', Exec isa nttOBY s t s' ∧ abiPreserved s s' ∧ nttOK.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : pR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : pR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa nttOBY s fun s' => PolyIs s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold nttOBY
    exact WP.mono (NttR.nttR_ok NttR.check_r10 (.inr rfl) hw hrf hwt hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2)
      fun s' ⟨hP, hf, _⟩ => ⟨hP, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .r8, .r9] hW (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)), hP⟩

/-- `nttOK` of the polynomial of `u16`s at `rdi` (512 bytes). -/
def nttO16K : Contract isa where
  pre s :=
    s.rd = [sR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .r10), pR (s.gpr .rsi)] ∧
    (sR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .r10)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .r10)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ ReducedW 16 s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .r10) (ntt (polyAtW 16 s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem nttOBY16_correct (s : State) (hs : nttO16K.pre s) :
    ∃ t s', Exec isa (nttR16 NttR.passBsR10) s t s' ∧ abiPreserved s s' ∧ nttO16K.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : pR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : sR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa (nttR16 NttR.passBsR10) s fun s' =>
      PolyIs s'.mem (s.gpr .r10) (ntt (polyAtW 16 s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem :=
    WP.mono (NttR.nttR16_ok NttR.check_r10 (.inr rfl) hw hrf hwt hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2)
      fun s' ⟨hP, hf, _⟩ => ⟨hP, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .r8, .r9] hW (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)), hP⟩

theorem BodiesOk.avx2 : BodiesOk .avx2 accY tabY :=
  ⟨nttOBY_correct, nttInvAccY_correct, zeroAccY_correct, fun _ _ _ hs => MulAccY.correct hs,
    fun s hin => tabAccY_wp s hin, ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ => (by decide +kernel : mulAccY.noCalls = true)⟩,
    finAccY_correct, by decide +kernel, fun _ hs => MulSetY.correct hs, by decide +kernel⟩

end VG.Proof.MlKem.X86_64
