module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicPowerLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerInit
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Impl.Mont.X86.CombPower
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.CombTableState
meta import VerifiedGarbage.Proof.Mont.X86.CombTableState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! Timing of public exponentiation through initialization, the comb loop and decoding. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem powerInit_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerInit n e (context n))
      (VG.Taint.hintOf taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerInit n e (context n)))).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> taint_decide

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
    obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (powerInit_check h)
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
