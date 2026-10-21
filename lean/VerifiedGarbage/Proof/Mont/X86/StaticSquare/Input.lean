module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.InputProducts
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Double
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Product

/-! # A symmetric input column, including its diagonal -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.StaticSquare

 theorem input_ok {s : State} {W : Addr} {L a N k : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat=W.toNat)
    (argA : (A 7).toNat=a) (fits : a+4*N≤L) (hk : k<2*N)
    (zero : value s=0)
    (bound : Column.coeff (fun i => w32 s.mem W (a+4*i)) (fun i => w32 s.mem W (a+4*i)) N k<2^96) :
    WP isa (.block (input N k)) s fun t =>
      value t=Column.coeff (fun i => w32 s.mem W (a+4*i)) (fun i => w32 s.mem W (a+4*i)) N k ∧
      Keeps [.eax,.edx,.edi,.esi,.ebx,.ecx] s t ∧ t.mem=s.mem := by
  have splitC := Column.coeff_square (fun i => w32 s.mem W (a+4*i)) N k
  have diag := Column.diagCoeff_value (fun i => w32 s.mem W (a+4*i)) N k
  unfold input
  split
  · next active =>
    simp only [List.append_assoc]
    refine WP.block_append (WP.mono (ptr_ok ha (r:=.edi) (t:=.eax) (i:=7) (by decide) (by decide) (by decide))
      fun u ⟨pu,_,mu,ku⟩ => ?_)
    have hu := hw.of_keeps ku
    have ptr : PtrAt u W .edi a := by rw [PtrAt,pu,BitVec.toNat_add,base,argA]
    have vu : value u=0 := by
      rw [value,ku.1 .esi (by decide),ku.1 .ebx (by decide),ku.1 .ecx (by decide)]
      exact zero
    have sumBound : value u+inputSum u.mem W a N k N<2^96 := by
      rw [vu,mu,inputSum_full]
      omega
    refine WP.block_append (WP.mono (inputProducts_ok u hu ptr fits (Nat.le_refl _) sumBound)
      fun v ⟨vv,kv,mv⟩ => ?_)
    have vv' : value v=Column.crossCoeff (fun i => w32 s.mem W (a+4*i)) N k := by
      rw [vv,vu,Nat.zero_add,mu,inputSum_full]
    refine WP.block_append (WP.mono (double_ok v (by rw [vv']; omega)) fun x ⟨vx,kx,mx⟩ => ?_)
    have vx' : value x=2*Column.crossCoeff (fun i => w32 s.mem W (a+4*i)) N k := by rw [vx,vv']
    have K : Keeps [.eax,.edx,.edi,.esi,.ebx,.ecx] s x :=
      ((ku.mono (by decide)).trans (kv.mono (by decide))).trans (kx.mono (by decide))
    have mem : x.mem=s.mem := mx.trans (mv.trans mu)
    split
    · next even =>
      have hhalf : k/2<N := by omega
      have px : PtrAt x W .edi a := by
        rw [PtrAt,kx.1 .edi (by decide),kv.1 .edi (by decide)]
        exact ptr
      have boundX : value x+w32 x.mem W (a+4*(k/2))*w32 x.mem W (a+4*(k/2))<2^96 := by
        rw [vx',mem]
        rw [diag,ite_eq_left ⟨even,hhalf⟩] at splitC
        omega
      refine WP.mono (product_ok (hw.of_keeps K) px px (by decide) (by omega) (by omega) boundX)
        fun t ⟨vt,kt,mt⟩ => ⟨?_,K.trans (kt.mono (by decide)),mt.trans mem⟩
      rw [vt,vx',mem]
      rw [diag,ite_eq_left ⟨even,hhalf⟩] at splitC
      exact splitC.symm
    · next odd =>
      refine WP.block_nil ⟨?_,K,mem⟩
      rw [vx']
      rw [diag,ite_eq_right (by omega),Nat.add_zero] at splitC
      exact splitC.symm
  · next inactive =>
    refine WP.block_nil ⟨?_,Keeps.refl _ s,rfl⟩
    rw [zero,Column.coeff_range]
    symm
    apply NatSum.eq_zero
    intro i hi
    exact ite_eq_right (by omega)

end VG.Proof.Mont.X86.StaticSquare
