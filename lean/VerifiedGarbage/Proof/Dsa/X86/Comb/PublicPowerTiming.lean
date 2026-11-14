module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicPowerStepTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerLoop
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Impl.Mont.X86.CombPower
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.CombTableState
meta import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! ### `Dsa.X86.Comb.PublicPowerLoopTiming`, which only this module used -/

section

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
        have le : i+1≤rows e := by omega_using [hi]
        by_contra hn
        have eq : i+1=rows e := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨rows e-(i+1),by omega_using [hi],i+1,rfl,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨0,by omega_using [],(power_bounds h).1,S,T⟩

end VG.Proof.Dsa.X86.Comb

end

end


/-! Timing of public exponentiation through initialization, the comb loop and decoding. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem powerInit_check {n e : Nat} (h : Supported n e) :
    ∃ hint, (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerInit n e (context n)) hint).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨_, by taint_decide⟩

structure PublicPowerInput (n e m g x : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem
  exp : val32 s.mem base (slot n 8) e=x

theorem publicPower_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat) :
    RelCT isa (fun s t => PublicPowerInput n e m g x base s ∧ PublicPowerInput n e m g x base t)
      (VG.Impl.Mont.X86.Comb.combPower n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.combPower VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  let R := fun s t => PowerLoop n e m g x 0 base s s ∧ PowerLoop n e m g x 0 base t t
  refine RelCT.seq (R := R) ?_ (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_
    (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) (checkedProgramChange (mul_check false _ _ _ _ _ _) rfl)
      (RelCT.block_nil (fun _ _ h => h))))
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (powerInit_check h).choose_spec
    have CT := checkedProgramChange check le
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    obtain ⟨Cs,Ts,As,Xs,Is,_,_⟩ := wp_result (powerInit_ok h S.ctx S.table) Es
    obtain ⟨Ct,Tt,At,Xt,It,_,_⟩ := wp_result (powerInit_ok h T.ctx T.table) Et
    have bound : x<2^(32*e) := S.exp ▸ val32_lt s.mem base (slot n 8) e
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,
      powerLoop_initial h Cs Ts As (Xs.trans S.exp) bound Is,
      powerLoop_initial h Ct Tt At (Xt.trans T.exp) bound It⟩
  · intro s t tr ur sf tf P Es Et
    exact publicPowerLoop_relCT h base m g x s t _ _ _ _ _ _ P Es Et

end VG.Proof.Dsa.X86.Comb
