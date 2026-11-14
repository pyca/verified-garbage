module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! The actual outer loop runs all nonfinal digits, in descending order. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_loop_ok {base table : Addr} {k : Nat}
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩) :
    ∀(n : Nat) (s : State),n<104 → WindowData base table k s →
      canonicalPoint s.mem base 1072 → s.gpr .x19=BitVec.ofNat 64 (n+2) →
      WP isa loop23 s fun t =>
        canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=
          windowNonfinal s.mem table k (n+1) (ordinaryPoint s.mem base 1072) ∧
        WindowData base table k t ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowStepPublic s t ∧
        t.gpr .x19=1#64 ∧ t.gpr .x4=0#64
  | 0,s,_,data,bound,counter => by
    have body := window_iteration_source.mp (window_iteration_ok data (j:=1) (by decide) apart bound counter)
    obtain ⟨trace,t,exec,b,p,d,f,pub,c19,c4⟩ := body
    have cond : isa.eval (.nonzero .x .x4) t=some false := by
      change some (t.gpr .x4 != 0)=some false
      rw [c4]; rfl
    refine ⟨_,t,Exec.loopExit exec cond,b,?_,d,f,pub,c19,?_⟩
    · simpa only [windowNonfinal,windowStepValue,windowFiveValue] using p
    · rw [c4]; rfl
  | n+1,s,hn,data,bound,counter => by
    have body := window_iteration_source.mp
      (window_iteration_ok data (j:=n+2) (by omega_arith) apart bound counter)
    obtain ⟨trace,u,exec,b,p,d,f,pub,c19,c4⟩ := body
    have cond : isa.eval (.nonzero .x .x4) u=some true := by
      change some (u.gpr .x4 != 0)=some true
      rw [c4]
      exact congrArg some (bne_iff_ne.mpr (window_counter_positive (n+2) (by omega_arith) (by omega_arith)))
    obtain ⟨trace',t,exec',bt,pt,dt,ft,kt,t19,t4⟩ := window_loop_ok apart n u (by omega_arith) d b c19
    refine ⟨_,t,Exec.loopNext exec cond exec',bt,?_,dt,WindowPhaseFrame.trans f ft,pub.trans kt,t19,t4⟩
    · rw [WindowPhaseFrame.run f apart k (n+1)] at pt
      rw [pt,p]
      rfl

 theorem window_loop_104 {s : State} {base table : Addr} {k : Nat}
    (data : WindowData base table k s) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64) :
    WP isa windowLoop s fun t =>
      canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=
        windowNonfinal s.mem table k 104 (ordinaryPoint s.mem base 1072) ∧
      WindowData base table k t ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowStepPublic s t ∧
      t.gpr .x19=1#64 ∧ t.gpr .x4=0#64 := by
  have h := window_loop_ok apart 103 s (by decide) data bound counter
  simpa only [windowLoop,sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] using h

end VG.Proof.Weierstrass.AArch64.P521Native
