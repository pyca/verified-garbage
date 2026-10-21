module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Init
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Rows
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Finish
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Rt.Save

/-! # The complete square before the shared final subtraction -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

 theorem front_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) {N S m inv o a : Nat}
    (V : ArgVals A W N S m inv o a a) (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a)
    (np : 0<N) (nl : N≤128) (hinv : (val32 s.mem W m N*w32 s.mem W inv+1)%2^32=0)
    (hlt : val32 s.mem W a N<val32 s.mem W m N) :
    WP isa (.seq (.block VG.Impl.Mont.X86.Rt.StaticSquare.init)
      (.seq (VG.Impl.Mont.X86.Rt.StaticSquare.columns N 0 (2*N))
        (.block (VG.Impl.Mont.X86.Rt.StaticSquare.finish N)))) s fun t =>
      Outs W [(S,12*N+56)] s.mem t.mem ∧ SavedAt t.mem W S s.gpr ∧ PtrAt t W .ebp (S+52+4*N) ∧
      val32 t.mem W (S+52+4*N) (N+1)<2*val32 s.mem W m N ∧
      (∃ q,2^(32*N)*val32 t.mem W (S+52+4*N) (N+1)=
        val32 s.mem W a N*val32 s.mem W a N+q*val32 s.mem W m N) ∧
      t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have nw := hw.nowrap
  have scr := lay.scr
  refine WP.seq (WP.mono (init_ok hw ha V.ws V.s V.inv (by omega) lay.inv_le
    (by have := lay.sinv; omega)) fun u ⟨pu,sv,ou,ku,iv,carry⟩ => ?_)
  have ou' : Outside W S (12*N+56) s.mem u.mem := ou.mono (Nat.le_refl _) (by omega)
  have hau := ha.of_keeps ku (by decide)
    (Outs.of_outside (ou'.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  have hu := hw.of_keeps ku
  have mv : val32 u.mem W m N=val32 s.mem W m N := ou'.val32 lay.smo (by have := lay.mo_le; omega)
  have av : val32 u.mem W a N=val32 s.mem W a N := ou'.val32 lay.sa (by have := lay.a_le; omega)
  have low : (w32 u.mem W m*w32 u.mem W (S+16)+1)%2^32=0 := by
    rw [iv]
    have source := Square.low_inverse s.mem W m inv np hinv
    have m0 : w32 u.mem W m=w32 s.mem W m := ou'.w32 (by have := lay.smo; omega) (by have := lay.mo_le; omega)
    rw [m0]
    exact source
  have start : ColsI u W L S m a N 0 0 u := by
    refine ⟨hu,Outside.refl _ _ _ _,Outs.refl _ _ _,Keeps.refl _ _,pu,carry,by omega,?_⟩
    simp only [Column.partSum_zero,Nat.zero_sub,val32,Nat.mul_zero,Nat.add_zero]
  refine WP.seq (WP.mono (columnsRun_ok hau V lay nl low start (by omega)) fun v ⟨c,I⟩ => ?_)
  simp only [Nat.zero_add] at I
  have final := I.final_bound (by rw [av,mv]; exact hlt)
  refine WP.mono (finish_ok I.ws I.edi (by omega) I.carry (by omega)) fun t ⟨ot,bp,vt,kt⟩ => ?_
  have O2 : Outside W S (12*N+56) v.mem t.mem := ot.mono (by omega) (by omega)
  have F2 : Outs W [(S+8,8),(S+52,8*N+8)] v.mem t.mem :=
    Outs.of_outside (ot.mono (by omega : S+52≤S+52+8*N) (by omega : S+52+8*N+8≤S+52+(8*N+8))) (by simp)
  have saved : SavedAt v.mem W S s.gpr := sv.of_outs I.frame (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have savedT := saved.of_outs F2 (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have K : Keeps columnClob s t := (ku.trans I.keep).trans (kt.mono (by decide))
  refine ⟨Outs.of_outside ((ou'.trans I.out).trans O2) (List.mem_singleton_self _),savedT,bp,?_,?_,
    K.1 _ (by decide),K.2.1,K.2.2⟩
  · rw [vt,←mv]
    exact final.1
  · refine ⟨val32 v.mem W (S+52) N,?_⟩
    rw [vt,←mv,←av,←Square.pow32]
    exact I.final_eq

end VG.Proof.Mont.X86.StaticSquare
