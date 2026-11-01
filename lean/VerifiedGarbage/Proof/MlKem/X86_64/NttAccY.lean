module
public import VerifiedGarbage.Proof.MlKem.X86_64.AccY
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR101
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR100
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-!
# ML-KEM on x86-64: `NTT` to an accumulator, with AVX2

`nttAccY` (`Impl/MlKem/X86_64/KpkeMul.lean`) is `vg_mlkem_ntt_avx2`'s code
storing `NTT` of the polynomial at `rdi` to the accumulator at `r10`, in
`vbase`'s order (`Acc16`), which the rows of `encryptMulYg` and `Kpke16.dmInnerY`
read as it is; it meets `nttAccK` (`NttR.nttRAcc_ok`). `nttAccY16` reads the
polynomial as `u16`s, and meets `nttAcc16K` (`NttR.nttRAcc16_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `NTT` of `f = rdi` to the accumulator at `r10` (512 bytes), with the
working space at `rsi`. -/
def nttAccK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [sR (s.gpr .r10), pR (s.gpr .rsi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (sR (s.gpr .r10)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (sR (s.gpr .r10)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Acc16 s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
    ∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem nttAccY_correct (s : State) (hs : nttAccK.pre s) :
    ∃ t s', Exec isa KpkeMul.nttAccY s t s' ∧ abiPreserved s s' ∧ nttAccK.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : sR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : pR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa KpkeMul.nttAccY s fun s' => (Acc16 s'.mem (s.gpr .r10) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
      ∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ Frame [sR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold KpkeMul.nttAccY
    exact WP.mono (NttR.nttRAcc_ok NttR.checkAcc_r10 (.inr rfl) hw hrf hwt hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2)
      fun s' ⟨hP, hf, hk⟩ => ⟨⟨hP, fun r h1 h2 => hk.gpr (by simp [h1, h2])⟩, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .r8] hW (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)), hP⟩

/-- `nttAccK` of the polynomial of `u16`s at `rdi` (512 bytes). -/
def nttAcc16K : Contract isa where
  pre s :=
    s.rd = [sR (s.gpr .rdi)] ∧ s.wr = [sR (s.gpr .r10), pR (s.gpr .rsi)] ∧
    (sR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (sR (s.gpr .r10)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (sR (s.gpr .r10)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ ReducedW 16 s.mem (s.gpr .rdi)
  post s s' := Acc16 s'.mem (s.gpr .r10) (ntt (polyAtW 16 s.mem (s.gpr .rdi))) ∧
    ∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem nttAccY16_correct (s : State) (hs : nttAcc16K.pre s) :
    ∃ t s', Exec isa KpkeMul.nttAccY16 s t s' ∧ abiPreserved s s' ∧ nttAcc16K.post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwt : sR (s.gpr .r10) ∈ s.wr := by rw [hs.2.1]; simp
  have hrf : sR (s.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hs.1]; simp
  have hW : WP isa KpkeMul.nttAccY16 s fun s' => (Acc16 s'.mem (s.gpr .r10) (ntt (polyAtW 16 s.mem (s.gpr .rdi))) ∧
      ∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ Frame [sR (s.gpr .r10), pR (s.gpr .rsi)] s.mem s'.mem := by
    unfold KpkeMul.nttAccY16
    exact WP.mono (NttR.nttRAcc16_ok NttR.checkAcc_r10 (.inr rfl) hw hrf hwt hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2)
      fun s' ⟨hP, hf, hk⟩ => ⟨⟨hP, fun r h1 h2 => hk.gpr (by simp [h1, h2])⟩, hf⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .r8] hW (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hk (by decide) hf (by simpa using ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)), hP⟩

end VG.Proof.MlKem.X86_64
