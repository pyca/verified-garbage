module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PrepareCore
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateCore
import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout

/-! Common functional boundary for the public and private comb helpers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def coreRanges (prepare : Bool) (n e : Nat) : List (Nat × Nat) :=
  if prepare then prepareRanges n e else privateRanges n e

def canonical (n e m g : Nat) (base : Addr) (mem : Mem) : Prop :=
  Spec.Rsa.wordsAt mem (off base (context n)) (Spec.Dsa.FixedBaseComb.contextWords (layout n e))=
    Spec.Dsa.FixedBaseComb.context (layout n e) m g

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
