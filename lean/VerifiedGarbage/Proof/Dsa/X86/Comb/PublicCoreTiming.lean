module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicBuildTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
import VerifiedGarbage.Proof.Mont.X86.CombBuild

/-! Public preparation leaks only the modulus, generator, exponent and workspace address. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure PublicCoreInput (n e m g x : Nat) (base : Addr) (s : State) extends PublicSetupInput n e m base s where
  generator : wordsVal s.mem base (slot n 5) n=g
  exponent : val32 s.mem base (slot n 8) e=x

theorem publicCore_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => PublicCoreInput n e m g x base s ∧ PublicCoreInput n e m g x base t)
      (core true n e) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have shape : 128*n<2^32 := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  let B := fun (s : State) => PublicBuildInput n e m g base s ∧ val32 s.mem base (slot n 8) e=x
  unfold core
  simp only [ite_true]
  refine RelCT.seq (R := fun s t => PublicPowerInput n e m g x base s ∧ PublicPowerInput n e m g x base t)
    (RelCT.seq (R := fun s t => B s ∧ B t) ?_ ?_) (publicPower_relCT h base m g x)
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have step {u v : State} (U : PublicCoreInput n e m g x base u) {trace}
        (E : Exec isa (setup n) u trace v) : B v := by
      obtain ⟨C,One,R,O,_⟩ := wp_result (setup_ok U.scr (table_layout h).positive shape
        (by have L := table_layout h; have := L.apart; have := L.bound; omega) U.modulus hm odd) E
      have G : wordsVal v.mem base (slot n 5) n=g := by
        rw [wordsVal_eq_val32,O.val32 (by
          rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
          rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,U.generator]
      have X : val32 v.mem base (slot n 8) e=x := (O.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans U.exponent
      exact ⟨⟨C,One,R,G⟩,X⟩
    exact ⟨(publicSetup_relCT h base m hm odd _ _ _ _ _ _ ⟨S.toPublicSetupInput,T.toPublicSetupInput⟩ Es Et).1,
      step S Es,step T Et⟩
  · intro s t tr ur sf tf ⟨⟨S,Xs⟩,⟨T,Xt⟩⟩ Es Et
    have step {u v : State} (U : PublicBuildInput n e m g base u)
        (X : val32 u.mem base (slot n 8) e=x) {trace}
        (E : Exec isa (VG.Impl.Mont.X86.Comb.combBuild n e (context n)) u trace v) : PublicPowerInput n e m g x base v := by
      obtain ⟨C,_,_,T,O,_⟩ := wp_result (VG.Proof.Mont.X86.Comb.build_ok (table_layout h) U.ctx U.one U.r2
        (power_bounds h).1 (power_bounds h).2.1) E
      rw [U.generator] at T
      exact ⟨C,T,(O.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans X⟩
    exact ⟨(publicBuild_relCT h base m g _ _ _ _ _ _ ⟨S,T⟩ Es Et).1,step S Xs Es,step T Xt Et⟩

end VG.Proof.Dsa.X86.Comb
