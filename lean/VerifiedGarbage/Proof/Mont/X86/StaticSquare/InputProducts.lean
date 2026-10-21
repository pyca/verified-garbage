module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Product
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum

/-! # The fixed list of off-diagonal square products -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.StaticSquare

def inputSum (mem : Mem) (W : Addr) (a N k count : Nat) : Nat :=
 NatSum.sum (fun i => if i≤k ∧ k-i<N ∧ i<k-i then
   w32 mem W (a+4*i)*w32 mem W (a+4*(k-i)) else 0) count

 theorem inputProducts_ok {W : Addr} {L a N k count : Nat} (s : State)
    (hw : Ws s W L) (hp : PtrAt s W .edi a) (fits : a+4*N≤L) (hc : count≤N)
    (bound : value s+inputSum s.mem W a N k count<2^96) :
    WP isa (.block (inputProducts N k count)) s fun t =>
      value t=value s+inputSum s.mem W a N k count ∧
      Keeps [.eax,.edx,.esi,.ebx,.ecx] s t ∧ t.mem=s.mem := by
  induction count generalizing s with
  | zero =>
    exact WP.block_nil ⟨by simp [inputSum,NatSum.sum],Keeps.refl _ s,rfl⟩
  | succ count ih =>
    have sumStep : inputSum s.mem W a N k (count+1)=inputSum s.mem W a N k count+
      (if count≤k ∧ k-count<N ∧ count<k-count then
        w32 s.mem W (a+4*count)*w32 s.mem W (a+4*(k-count)) else 0) := rfl
    have boundPrefix : value s+inputSum s.mem W a N k count<2^96 := by rw [sumStep] at bound; omega
    have codeStep : inputProducts N k (count+1)=inputProducts N k count++inputTerm N k count := by
      simp only [inputProducts,List.range_succ,List.flatMap_append,List.flatMap_singleton]
    rw [codeStep]
    refine WP.block_append (WP.mono (ih s hw hp (by omega) boundPrefix) fun u ⟨vu,ku,mu⟩ => ?_)
    have hu := hw.of_keeps ku
    have pu : PtrAt u W .edi a := by rw [PtrAt,ku.1 .edi (by decide)]; exact hp
    unfold inputTerm
    split
    · next good =>
      have limit : value u+w32 u.mem W (a+4*count)*w32 u.mem W (a+4*(k-count))<2^96 := by
        rw [mu,vu]
        rw [sumStep,ite_eq_left good] at bound
        omega
      refine WP.mono (product_ok hu pu pu (by decide) (by omega) (by omega) limit) fun t ⟨vt,kt,mt⟩ => ?_
      refine ⟨?_,ku.trans kt,mt.trans mu⟩
      rw [vt,vu,mu,sumStep,ite_eq_left good,Nat.add_assoc]
    · next bad =>
      exact WP.block_nil ⟨by rw [vu,sumStep,ite_eq_right bad,Nat.add_zero],ku,mu⟩

 theorem inputSum_full (mem : Mem) (W : Addr) (a N k : Nat) :
    inputSum mem W a N k N=Column.crossCoeff (fun i => w32 mem W (a+4*i)) N k := by
  rw [Column.crossCoeff_range]
  rfl

end VG.Proof.Mont.X86.StaticSquare
