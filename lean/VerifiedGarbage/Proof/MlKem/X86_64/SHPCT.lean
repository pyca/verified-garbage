module

import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
public import VerifiedGarbage.Proof.MlKem.X86_64.SHP
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHP

/-!
# ML-KEM on x86-64: `Sample4.sampleP`, constant time but for the seeds

As `sampleH` (`SHCT.lean`): the code but for the loops and the checks of the
counts is proven by the taint analysis from the pointers, with every byte
of the states secret. `σ`, which the fourth state absorbs, flows only into
the states, the fourth buffer and the outputs of `PRF₂`, at fixed addresses;
the loops of both runs read the same output of the first three seeds.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (iterF)

/-- The start. -/
theorem startP_ct : RelCT isa (S4.R4W true fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
      ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)), .mov32 .r9 (.imm 0x1f00)] : List Instr)))
    (S4.R4W true fun σ s => PI true σ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact startP_ok (preW_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))

/-- The two squeezes with `PRF₂`. -/
theorem sqP_ct {fast : Bool} : RelCT isa (S4.R4W true fun σ s => PI true σ 0 s) (blocks oBuf 168 2 (squeezeP fast))
    (S4.R4W true fun σ s => PI true σ 2 s) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx, .r8]) (blocks oBuf 168 2 (squeezeP fast)) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => squeezesP_ok (fast := fast) (preW_of hp) h)
    (taintRel [.rbx, .r8] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      have hb := env_rbx hq h₁.sq.env h₂.sq.env
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · rw [h₁.r8, h₂.r8, poA, poA, at', at', ← h₁.sq.env.rbx, ← h₂.sq.env.rbx, hb]) c)

/-- The third squeeze. -/
theorem sq3P_ct {fast : Bool} : RelCT isa (S4.R4W true fun σ s => PI true σ 2 s) (squeezes 2 1 fast)
    (S4.R4W true fun σ s => SqY true σ (iterF 1 (Yp σ 2)) 0 3 s ∧ HP σ s.mem) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 2 1 fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => WP.mono (sqYs_ok (fast := fast) (preW_of hp) (b := 2) (n := 1) (by decide) (by decide) h.sq)
      fun _ ⟨h₃, f₃⟩ => ⟨h₃, HP.stab σ h.out f₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm⟩)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

theorem ctP {fast : Bool} : ConstantTime isa samplePKW.pre samplePKW.pub (sampleP fast) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq startP_ct (RelCT.seq (sqP_ct (fast := fast)) (RelCT.seq (sq3P_ct (fast := fast))
    (RelCT.seq (tabY_ct (Y := fun σ => iterF 1 (Yp σ 2)) (H := fun σ => HP σ) fun σ => HP.stab σ) ?_))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

end VG.Proof.MlKem.X86_64.SH
