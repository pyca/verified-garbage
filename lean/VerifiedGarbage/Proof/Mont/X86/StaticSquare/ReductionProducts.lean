module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Product
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum

/-! # The fixed list of Montgomery cancellation products -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.StaticSquare

def reductionSum (mem : Mem) (W : Addr) (S m N k count : Nat) : Nat :=
 NatSum.sum (fun i => if i<k ∧ k-i<N then
   w32 mem W (S+(52+4*i))*w32 mem W (m+4*(k-i)) else 0) count

 theorem reductionProducts_ok {W : Addr} {L S m N k count : Nat} (s : State)
    (hw : Ws s W L) (hp : PtrAt s W .edi S) (mp : PtrAt s W .ebp m)
    (fits : S+52+4*N≤L) (mfits : m+4*N≤L) (hc : count≤N)
    (bound : value s+reductionSum s.mem W S m N k count<2^96) :
    WP isa (.block (reductionProducts N k count)) s fun t =>
      value t=value s+reductionSum s.mem W S m N k count ∧
      Keeps [.eax,.edx,.esi,.ebx,.ecx] s t ∧ t.mem=s.mem := by
  induction count generalizing s with
  | zero =>
    exact WP.block_nil ⟨by simp [reductionSum,NatSum.sum],Keeps.refl _ s,rfl⟩
  | succ count ih =>
    have sumStep : reductionSum s.mem W S m N k (count+1)=reductionSum s.mem W S m N k count+
      (if count<k ∧ k-count<N then
        w32 s.mem W (S+(52+4*count))*w32 s.mem W (m+4*(k-count)) else 0) := rfl
    have boundPrefix : value s+reductionSum s.mem W S m N k count<2^96 := by rw [sumStep] at bound; omega
    have codeStep : reductionProducts N k (count+1)=reductionProducts N k count++reductionTerm N k count := by
      simp only [reductionProducts,List.range_succ,List.flatMap_append,List.flatMap_singleton]
    rw [codeStep]
    refine WP.block_append (WP.mono (ih s hw hp mp (by omega) boundPrefix) fun u ⟨vu,ku,mu⟩ => ?_)
    have hu := hw.of_keeps ku
    have pu : PtrAt u W .edi S := by rw [PtrAt,ku.1 .edi (by decide)]; exact hp
    have pm : PtrAt u W .ebp m := by rw [PtrAt,ku.1 .ebp (by decide)]; exact mp
    unfold reductionTerm
    split
    · next good =>
      have limit : value u+w32 u.mem W (S+(52+4*count))*w32 u.mem W (m+4*(k-count))<2^96 := by
        rw [mu,vu]
        rw [sumStep,ite_eq_left good] at bound
        omega
      refine WP.mono (product_ok hu pu pm (by decide) (by omega) (by omega) limit) fun t ⟨vt,kt,mt⟩ => ?_
      refine ⟨?_,ku.trans kt,mt.trans mu⟩
      rw [vt,vu,mu,sumStep,ite_eq_left good,Nat.add_assoc]
    · next bad =>
      exact WP.block_nil ⟨by rw [vu,sumStep,ite_eq_right bad,Nat.add_zero],ku,mu⟩

 theorem reductionSum_full (mem : Mem) (W : Addr) (S m N k : Nat) :
    reductionSum mem W S m N k N=Column.coeff
      (Column.prefixDigits (fun i => w32 mem W (S+52+4*i)) k)
      (fun i => w32 mem W (m+4*i)) N k := by
  rw [Column.coeff_range]
  apply NatSum.congr
  intro i hi
  by_cases lt : i<k
  · simp only [Column.prefixDigits,ite_eq_left lt]
    by_cases fit : k-i<N
    · simp only [lt,fit,and_self,ite_true,show i≤k by omega,Nat.add_assoc]
    · simp only [lt,fit,and_false,ite_false]
  · simp only [Column.prefixDigits,Nat.zero_mul,ite_self,lt,false_and,ite_false]

end VG.Proof.Mont.X86.StaticSquare
