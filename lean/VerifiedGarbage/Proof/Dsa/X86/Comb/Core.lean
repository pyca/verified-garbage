module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PrepareCore
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract

import VerifiedGarbage.Proof.Dsa.X86.Comb.Power
import VerifiedGarbage.Proof.Mont.X86.CombCanonical
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
/-! Common functional boundary for the public and private comb helpers. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PrivateCore.lean`, which only this module imported.
section

/-! Private powers reuse exactly the retained public context supplied by the caller. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

def privateRanges (n e : Nat) : List (Nat × Nat) := setupRanges n ++ powerRanges n e

theorem private_core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : Spec.Rsa.wordsAt s.mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
      Proof.Dsa.FixedBaseComb.context (layout n e) m (wordsVal s.mem base (slot n 5) n)) :
    WP isa (core false n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Outs base (privateRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have L := table_layout h
  have T : TableAt n (context n) m (wordsVal s.mem base (slot n 5) n) (32*e) base (fun _ => True) s.mem :=
    VG.Proof.Mont.X86.Comb.table_of_context (L := layout n e) (by omega)
      (hv ▸ wordsVal_lt s.mem base (slot n 0) n) H
  have size : contextBytes n≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold core
  simp only [Bool.false_eq_true,ite_false]
  refine WP.seq (WP.mono (contextStart_ok hs L.positive size hv hm odd) fun u ⟨Cu,One,Ou,Ku⟩ => ?_)
  have Tu := T.outs L hs Ou (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Eu : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := Ou.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  refine WP.mono (power_ok h false Cu Tu One) fun t ⟨_,V,O,K⟩ => ⟨by rw [V,Eu],?_,Ku.trans K⟩
  exact (Ou.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (O.mono (fun _ hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def coreRanges (prepare : Bool) (n e : Nat) : List (Nat × Nat) :=
  if prepare then prepareRanges n e else privateRanges n e

def canonical (n e m g : Nat) (base : Addr) (mem : Mem) : Prop :=
  Spec.Rsa.wordsAt mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
    Proof.Dsa.FixedBaseComb.context (layout n e) m g

theorem core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (prepare : Bool) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base s.mem) :
    WP isa (core prepare n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base t.mem) ∧
      Outs base (coreRanges prepare n e) s.mem t.mem ∧ Keeps powerClob s t := by
  cases prepare with
  | true => exact WP.mono (prepare_core_ok h hs hv hm odd) fun t ⟨V,C,O,K⟩ => ⟨V,fun _ => C,O,K⟩
  | false => exact WP.mono (private_core_ok h hs hv hm odd (H rfl)) fun t ⟨V,O,K⟩ => ⟨V,(fun eq => Bool.noConfusion eq),O,K⟩

end VG.Proof.Dsa.X86.Comb
