module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSelectTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Mont.X86.CombPower
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! A public comb step uses the same public digit in both executions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem powerDigits_check {n e : Nat} (h : Supported n e) :
    ∃ hint, (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerDigits n e) hint).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨_, by taint_decide⟩

theorem powerDigits_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (VG.Impl.Mont.X86.Comb.powerDigits n e)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (powerDigits_check h).choose_spec
  exact checkedProgramChange check le

structure PublicPowerState (n e m g E x : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem
  acc : wordsVal s.mem base (slot n 6) n=Spec.Rsa.powMod g E m*2^(64*n)%m
  exp : val32 s.mem base (slot n 8) (expWords e)=x

theorem publicPowerLookup_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g E x : Nat) :
    RelCT isa (fun s t => PublicPowerState n e m g E x base s ∧ PublicPowerState n e m g E x base t)
      (VG.Impl.Mont.X86.Comb.powerLookup n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.powerLookup VG.Impl.Mont.X86.Comb.seq
  simp only [ite_true,List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (R := WordPair base (layout n e).size) ?_
    (RelCT.seq (publicSelect_relCT _ _ _ _ _ (power_bounds h).2.2.2.2.2.2) (RelCT.block_nil (fun _ _ h => h)))
  intro s t tr ur sf tf ⟨S,T⟩ Es Et
  have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
  have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
  obtain ⟨Cs,_,_,_,Ws,_,_⟩ := wp_result (powerDigits_ok h S.ctx S.table S.acc) Es
  obtain ⟨Ct,_,_,_,Wt,_,_⟩ := wp_result (powerDigits_ok h T.ctx T.table T.acc) Et
  exact ⟨(powerDigits_relCT h _ _ _ _ _ _ A Es Et).1,Cs.scr,Ct.scr,by rw [Ws,Wt,S.exp,T.exp]⟩

theorem publicPowerStep_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g E x : Nat) :
    RelCT isa (fun s t => PublicPowerState n e m g E x base s ∧ PublicPowerState n e m g E x base t)
      (VG.Impl.Mont.X86.Comb.powerStep n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.powerStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (publicPowerLookup_relCT h base m g E x) (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_)
  · exact checkedProgramChange (mul_check false _ _ _ _ _ _) rfl
  · exact RelCT.seq (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl)
      (RelCT.block_nil (fun _ _ h => h))

end VG.Proof.Dsa.X86.Comb
