module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicPowerStepTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerLoop
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

/-! Equal public exponents follow the same fixed-count comb loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.FixedBaseComb (high)

theorem publicPowerLoop_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat) (s₀ t₀ : State) :
    RelCT isa (fun s t => PowerLoop n e m g x 0 base s₀ s ∧ PowerLoop n e m g x 0 base t₀ t)
      (.loop (VG.Impl.Mont.X86.Comb.powerStep n e (context n) true) .ne)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let I (remaining : Nat) (s t : State) : Prop := ∃ i, remaining=rows e-i ∧ i<rows e ∧
    PowerLoop n e m g x i base s₀ s ∧ PowerLoop n e m g x i base t₀ t
  refine (RelCT.loop I ?_ (rows e)).mono ?_ (fun _ _ h => h)
  · intro remaining s t tr ur sf tf ⟨i,eq,hi,S,T⟩ E F
    subst remaining
    have pair : PublicPowerState n e m g (high (32*e) x (rows e-i)) (x*2^i%2^(32*expWords e)) base s ∧
        PublicPowerState n e m g (high (32*e) x (rows e-i)) (x*2^i%2^(32*expWords e)) base t :=
      ⟨⟨S.ctx,S.table,S.acc,S.exp⟩,⟨T.ctx,T.table,T.acc,T.exp⟩⟩
    obtain ⟨Trace,Agree⟩ := publicPowerStep_relCT h base m g _ _ _ _ _ _ _ _ pair E F
    obtain ⟨S',Zs⟩ := wp_result (powerLoop_step h true hi S) E
    obtain ⟨T',Zt⟩ := wp_result (powerLoop_step h true hi T) F
    refine ⟨Trace,?_,fun _ => Agree,?_⟩
    · change VG.X86.eval .ne sf=VG.X86.eval .ne tf
      simp only [VG.X86.eval,Zs,Zt]
    · intro hc
      have next : i+1<rows e := by
        have le : i+1≤rows e := by omega
        by_contra hn
        have eq : i+1=rows e := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨rows e-(i+1),by omega,i+1,rfl,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨0,by omega,(power_bounds h).1,S,T⟩

end VG.Proof.Dsa.X86.Comb
