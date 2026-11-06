module

import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
public import VerifiedGarbage.Proof.MlKem.X86_64.SHP
meta import VerifiedGarbage.Proof.MlKem.X86_64.SHP

/-!
# ML-KEM on x86-64: `Sample4.samplePN`, constant time but for the seeds

As `sampleH` (`SHCT.lean`): the code but for the loops and the checks of the
counts is proven by the taint analysis from the pointers, with every byte
of the states secret. `σ`, which the fourth state absorbs, flows only into
the states, the fourth buffer and the outputs of `PRF₂`, at fixed addresses;
the loops of both runs read the same output of the first three seeds.
`ctPN` takes the taint analysis of the parts that depend on `N₀` and `m`,
which the kernel evaluates for each of `Sample4.pnUses` (`ctPN_uses`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.Sha3 (iterF)

/-- The start. -/
theorem startP_ct {N₀ : Nat} (hN : N₀ < 256) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx])
      (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
        ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
          .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr))) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
      ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
        .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr)))
    (S4.R4W true fun σ s => PI true σ N₀ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact startP_ok (preW_of hp) hN)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) c)

/-- The `m` squeezes with `PRF₂`. -/
theorem sqP_ct {fast : Bool} {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3) (hN : N₀ + m ≤ 256)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r8]) (blocks oBuf 168 m (squeezeP fast)) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => PI true σ N₀ 0 s) (blocks oBuf 168 m (squeezeP fast))
      (S4.R4W true fun σ s => PI true σ N₀ m s) :=
  relInv (fun σ s hp h => squeezesP_ok (fast := fast) (preW_of hp) hm hm' hN h)
    (taintRel [.rbx, .r8] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      have hb := env_rbx hq h₁.sq.env h₂.sq.env
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · rw [h₁.r8, h₂.r8, poA, poA, at', at', ← h₁.sq.env.rbx, ← h₂.sq.env.rbx, hb]) c)

/-- The squeezes after them. -/
theorem sq3P_ct {fast : Bool} {N₀ m : Nat} (hm' : m ≤ 3) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (if m = 3 then .block [] else squeezes m (3 - m) fast) hc).isSome = true) :
    RelCT isa (S4.R4W true fun σ s => PI true σ N₀ m s) (if m = 3 then .block [] else squeezes m (3 - m) fast)
      (S4.R4W true fun σ s => SqY true σ (iterF (3 - m) (Yp σ N₀ m)) 0 3 s ∧ HP σ N₀ m s.mem) :=
  relInv (fun σ s hp h => restP_ok (fast := fast) (preW_of hp) hm' h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

theorem ctPN {fast : Bool} {N₀ m : Nat} (hm : 0 < m) (hm' : m ≤ 3) (hN : N₀ + m ≤ 256)
    {h₁ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx])
      (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4 ++
        ([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)),
          .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))] : List Instr))) h₁).isSome = true)
    {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r8]) (blocks oBuf 168 m (squeezeP fast)) h₂).isSome = true)
    {h₃ : VG.Taint.Hint X86_64.Taint.T}
    (c₃ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (if m = 3 then .block [] else squeezes m (3 - m) fast) h₃).isSome = true) :
    ConstantTime isa (samplePNKW N₀ m).pre (samplePNKW N₀ m).pub (samplePN fast N₀ m) := by
  unfold samplePN
  rw [ifn (show ¬ m = 0 by omega_arith)]
  refine relStart (Q := fun _ _ => True) (RelCT.seq (startP_ct (by omega_arith) c₁) (RelCT.seq (sqP_ct hm hm' hN c₂)
    (RelCT.seq (sq3P_ct hm' c₃)
    (RelCT.seq (tabY_ct (Y := fun σ => iterF (3 - m) (Yp σ N₀ m)) (H := fun σ => HP σ N₀ m) fun σ => HP.stab σ hm') ?_))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

theorem ctPN_uses {fast : Bool} {q : Nat × Nat} (hq : q ∈ pnUses) :
    ConstantTime isa (samplePNKW q.1 q.2).pre (samplePNKW q.1 q.2).pub (samplePN fast q.1 q.2) := by
  simp only [pnUses, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> cases fast <;>
    exact ctPN (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.MlKem.X86_64.SH
