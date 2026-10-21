module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Body
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.Covers

/-! Lift the fixed workspace proof to any allocation large enough for the helper. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem body_noCalls {n e : Nat} (h : Supported n e) (prepare : Bool) :
    (body prepare n e).noCalls=true := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel

def narrowState (n e : Nat) (base : Addr) (s : State) : State :=
  s.withRegions (s.rd++s.wr) [⟨base,(layout n e).size⟩]

theorem narrowResources {n e size : Nat} {base : Addr} {s : State}
    (E : Pow.Entry s base size) (hz : (layout n e).size≤size) :
    Pow.Entry (narrowState n e base s) base (layout n e).size ∧
      Covers ((s.rd++s.wr)++[⟨base,(layout n e).size⟩]) (s.rd++s.wr) ∧
      Covers [⟨base,(layout n e).size⟩] s.wr := by
  let rd := s.rd++s.wr
  let wr : List Region := [⟨base,(layout n e).size⟩]
  have En : Pow.Entry (s.withRegions rd wr) base (layout n e).size := by
    refine ⟨?_,E.base_eq,List.mem_singleton_self _,?_,?_⟩
    · obtain ⟨r,hr,hc⟩ := E.arg
      exact ⟨r,List.mem_append_left _ hr,hc⟩
    · have := E.nowrap; omega
    · have := E.stk
      change StkOk (s.gpr .esp) base (layout n e).size
      unfold StkOk at *; omega
  have writable : Covers wr s.wr := Covers.one ⟨⟨base,size⟩,E.wr,by
    change (base-base).toNat+(layout n e).size≤size
    simpa only [BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add] using hz⟩
  have readable : Covers (rd++wr) (s.rd++s.wr) := Covers.append_left (Covers.refl _)
    (writable.trans (Covers.of_mem (fun _ hr => List.mem_append_right _ hr)))
  exact ⟨En,readable,writable⟩

theorem body_wide_ok {n e m size : Nat} {base : Addr} {s : State}
    (h : Supported n e) (prepare : Bool) (E : Pow.Entry s base size) (hz : (layout n e).size≤size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base s.mem) :
    WP isa (body prepare n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base t.mem) ∧
      Outs base (scratch prepare n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  obtain ⟨En,readable,writable⟩ := narrowResources E hz
  exact WP.narrow (body_ok h prepare En hv hm odd H) readable writable
    (fun t R W _ ⟨V,C,O,K,_,_⟩ => ⟨V,C,O,K,R,W⟩) (body_noCalls h prepare)

end VG.Proof.Dsa.X86.Comb
