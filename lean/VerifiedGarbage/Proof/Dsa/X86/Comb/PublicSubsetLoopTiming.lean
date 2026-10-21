module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSubsetTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicColumnTiming
public import VerifiedGarbage.Proof.Mont.X86.CombSubsets
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Mont.X86.CombSubsets
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

/-! The subset construction loop has exactly 31 public iterations. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (Subsets TableAt knownSubset)

theorem publicSubsetLoop_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) (s₀ t₀ : State) :
    RelCT isa (fun s t => Subsets n (context n) (layout n e).size m g (32*e) 1 base s₀ s ∧
      Subsets n (context n) (layout n e).size m g (32*e) 1 base t₀ t)
      (.loop (VG.Impl.Mont.X86.Comb.subsetStep n (context n+16*n)) .ne)
      (VG.X86.Taint.Agree columnIndex) := by
  let I (remaining : Nat) (s t : State) : Prop := ∃ a, remaining=32-a ∧ 0<a ∧ a<32 ∧
    Subsets n (context n) (layout n e).size m g (32*e) a base s₀ s ∧
    Subsets n (context n) (layout n e).size m g (32*e) a base t₀ t
  refine (RelCT.loop I ?_ 31).mono ?_ (fun _ _ h => h)
  · intro remaining s t tr ur sf tf ⟨a,eq,ha,hi,S,T⟩ E F
    subst remaining
    obtain ⟨Trace,Agree⟩ := publicSubsetStep_relCT h base a ha hi _ _ _ _ _ _ ⟨S.ctx.scr,T.ctx.scr,S.count,T.count⟩ E F
    obtain ⟨S',Zs⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetStep_ok (table_layout h) S ha hi) E
    obtain ⟨T',Zt⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetStep_ok (table_layout h) T ha hi) F
    refine ⟨Trace,?_,fun _ => Agree,?_⟩
    · change VG.X86.eval .ne sf=VG.X86.eval .ne tf
      simp only [VG.X86.eval,Zs,Zt]
    · intro hc
      have next : a+1<32 := by
        by_contra hn
        have eq : a+1=32 := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨32-(a+1),by omega,a+1,rfl,by omega,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨1,rfl,by decide,by decide,S,T⟩

structure PublicSubsetsInput (n e m g : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (knownSubset 1) s.mem

theorem publicSubsets_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) :
    RelCT isa (fun s t => PublicSubsetsInput n e m g base s ∧ PublicSubsetsInput n e m g base t)
      (VG.Impl.Mont.X86.Comb.buildSubsets n (context n))
      (VG.X86.Taint.Agree columnIndex) := by
  unfold VG.Impl.Mont.X86.Comb.buildSubsets
  let R := fun (s t : State) => ∃ s₀ t₀,
    Subsets n (context n) (layout n e).size m g (32*e) 1 base s₀ s ∧
    Subsets n (context n) (layout n e).size m g (32*e) 1 base t₀ t
  refine RelCT.seq (R := R) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    have CT : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
        (.block [.mov .esi (VG.Impl.Mont.X86.Comb.imm 1)])
        (VG.X86.Taint.Agree (workspaceTaint false)) := checkedProgramChange (hint := .block []) rfl rfl
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,s,t,
      wp_result (VG.Proof.Mont.X86.Comb.buildSubsets_initial S.ctx S.table) Es,
      wp_result (VG.Proof.Mont.X86.Comb.buildSubsets_initial T.ctx T.table) Et⟩
  · intro s t tr ur sf tf ⟨s₀,t₀,S,T⟩ Es Et
    exact publicSubsetLoop_relCT h base m g s₀ t₀ _ _ _ _ _ _ ⟨S,T⟩ Es Et

end VG.Proof.Dsa.X86.Comb
