module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSubsetLoopTiming
import VerifiedGarbage.Proof.Mont.X86.CombBuild
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicColumnTiming
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicColumnTiming
public import VerifiedGarbage.Impl.Mont.X86.CombTable
meta import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
meta import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Mont.X86.CombStart
meta import VerifiedGarbage.Proof.Mont.X86.CombStart

/-! Public preparation builds the shared comb table with public-only addressing. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem buildStart_check {n e : Nat} (h : Supported n e) :
    ∃ hint, (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.buildStart n (context n)) hint).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨_, by taint_decide⟩

structure PublicBuildInput (n e m g : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  one : wordsVal s.mem base (slot n 3) n=1
  r2 : wordsVal s.mem base (slot n 4) n=2^(128*n)%m
  generator : wordsVal s.mem base (slot n 5) n=g

theorem publicBuild_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) :
    RelCT isa (fun s t => PublicBuildInput n e m g base s ∧ PublicBuildInput n e m g base t)
      (VG.Impl.Mont.X86.Comb.combBuild n e (context n))
      (VG.X86.Taint.Agree columnIndex) := by
  let P := fun (s : State) => PublicColumnsInput n e m g base s ∧
    wordsVal s.mem base (context n+16*n) n=2^(64*n)%m
  unfold VG.Impl.Mont.X86.Comb.combBuild VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (R := fun s t => P s ∧ P t) ?_
    (RelCT.seq (R := fun s t => PublicSubsetsInput n e m g base s ∧ PublicSubsetsInput n e m g base t) ?_
      (RelCT.seq (publicSubsets_relCT h base m g) (RelCT.block_nil (fun _ _ h => h))))
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (buildStart_check h).choose_spec
    have CT := checkedProgramChange check le
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    have step {u v : State} (U : PublicBuildInput n e m g base u) {trace}
        (E : Exec isa (VG.Impl.Mont.X86.Comb.buildStart n (context n)) u trace v) : P v := by
      obtain ⟨C,_,_,Z,G,V,_,_⟩ := wp_result (VG.Proof.Mont.X86.Comb.buildStart_ok (table_layout h) U.ctx U.one U.r2) E
      have initial : VG.Proof.Mont.X86.Comb.columnValue n m g (rows e) 0=g*2^(64*n)%m := by
        simp only [VG.Proof.Mont.X86.Comb.columnValue,Nat.mul_zero,Nat.pow_zero,
          VG.Proof.Bignum.powMod_eq,Nat.pow_one]
        exact Nat.mod_mul_mod _ _ _
      rw [U.generator] at G V
      exact ⟨⟨C,V.trans initial.symm,G.trans initial.symm⟩,Z⟩
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,step S Es,step T Et⟩
  · intro s t tr ur sf tf ⟨⟨S,Zs⟩,⟨T,Zt⟩⟩ Es Et
    obtain Is := wp_result (VG.Proof.Mont.X86.Comb.buildColumns_ok (table_layout h) S.ctx
      (power_bounds h).1 (power_bounds h).2.1 S.value S.entry) Es
    obtain It := wp_result (VG.Proof.Mont.X86.Comb.buildColumns_ok (table_layout h) T.ctx
      (power_bounds h).1 (power_bounds h).2.1 T.value T.entry) Et
    exact ⟨(publicColumns_relCT h base m g _ _ _ _ _ _ ⟨S,T⟩ Es Et).1,
      ⟨Is.ctx,Is.tableAt (table_layout h) S.ctx.scr.nowrap Zs⟩,
      ⟨It.ctx,It.tableAt (table_layout h) T.ctx.scr.nowrap Zt⟩⟩

end VG.Proof.Dsa.X86.Comb
