module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Power
import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
import VerifiedGarbage.Proof.Mont.X86.CombCanonical
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Mont.X86.CombBuild
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Mont.X86.CombBuild

/-! Public preparation constructs a canonical table and returns the public power. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt buildRanges)

def prepareRanges (n e : Nat) : List (Nat × Nat) :=
  setupRanges n ++ buildRanges n (context n) ++ powerRanges n e

theorem prepare_core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1) :
    WP isa (core true n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Spec.Rsa.wordsAt t.mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
        Proof.Dsa.FixedBaseComb.context (layout n e) m (wordsVal s.mem base (slot n 5) n) ∧
      Outs base (prepareRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have L := table_layout h
  have shape : 128*n<2^32 ∧ contextBytes n≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold core
  simp only [ite_true]
  refine WP.seq (WP.seq (WP.mono (setup_ok hs L.positive shape.1 shape.2 hv hm odd)
    fun u ⟨Cu,Oneu,Ru,Ou,Ku⟩ => ?_))
  have Gu : wordsVal u.mem base (slot n 5) n=wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32,wordsVal_eq_val32]
    exact Ou.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Eu : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := Ou.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  refine WP.mono (VG.Proof.Mont.X86.Comb.build_ok L Cu Oneu Ru (power_bounds h).1 (power_bounds h).2.1)
    fun v ⟨Cv,Pv,Rv,Tv,Ov,Kv⟩ => ?_
  rw [Gu] at Tv
  have Ev : val32 v.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := (Ov.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans Eu
  have Onev : wordsVal v.mem base (slot n 3) n=1 := by
    rw [wordsVal_eq_val32,Ov.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Oneu]
  refine WP.mono (power_ok h true Cv Tv Onev) fun t ⟨_,Vt,Ot,Kt⟩ => ?_
  refine ⟨by rw [Vt,Ev],?_,?_,(Ku.trans Kv).trans Kt⟩
  · have Pt : wordsVal t.mem base (context n) n=m := by
      rw [wordsVal_eq_val32,Ot.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Pv]
    have Rt : wordsVal t.mem base (context n+8*n) n=2^(128*n)%m := by
      rw [wordsVal_eq_val32,Ot.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Rv]
    exact VG.Proof.Mont.X86.Comb.context_canonical (L := layout n e) Pt Rt (power_preserves_table h Cv.scr Tv Ot)
  · have a : Outs base (prepareRanges n e) s.mem u.mem := Ou.mono (by
      intro r hr; exact List.mem_append_left _ (List.mem_append_left _ hr))
    have b : Outs base (prepareRanges n e) u.mem v.mem := Ov.mono (by
      intro r hr; exact List.mem_append_left _ (List.mem_append_right _ hr))
    have c : Outs base (prepareRanges n e) v.mem t.mem := Ot.mono (fun _ hr => List.mem_append_right _ hr)
    exact (a.trans b).trans c

end VG.Proof.Dsa.X86.Comb
