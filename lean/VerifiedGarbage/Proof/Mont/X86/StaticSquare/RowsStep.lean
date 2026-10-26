module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Column
public import VerifiedGarbage.Proof.Mont.X86.Square.RedMath
import VerifiedGarbage.Proof.Mont.X86.Square.RowsMath
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Util.CompileInductive

/-! # The polynomial invariant between fixed square columns -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Square (mDigits qDigits)

structure ColsI (s : State) (W : Addr) (L S m a N k c : Nat) (t : State) : Prop where
  ws : Ws t W L
  out : Outside W S (12*N+56) s.mem t.mem
  frame : Outs W [(S+8,8),(S+52,8*N+8)] s.mem t.mem
  keep : Keeps columnClob s t
  edi : PtrAt t W .edi S
  carry : w32 t.mem W (S+8)+2^32*w32 t.mem W (S+12)=c
  bound : c≤4*N*2^32
  equation : (2^32)^k*c+(2^32)^N*val32 t.mem W (S+52+4*N) (k-N)=
    Column.partSum (2^32) (mDigits s W a) (mDigits s W a) N k+
    Column.partSum (2^32) (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k

 theorem iterate_ok {s t : State} {W : Addr} {L S m inv a o N k c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (nl : N≤128)
    (hinv : (w32 s.mem W m*w32 s.mem W (S+16)+1)%2^32=0)
    (I : ColsI s W L S m a N k c t) (hk : k<2*N) :
    WP isa (VG.Impl.Mont.X86.Rt.StaticSquare.column N k) t fun u =>
      ColsI s W L S m a N (k+1) (total t.mem W a S m N k c/2^32) u := by
  have nw := I.ws.nowrap
  have scr := lay.scr
  have np : 0<N := by omega
  have haT := ha.of_keeps I.keep (by decide)
    (Outs.of_outside (I.out.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  have af := Square.digits_frame nw lay.a_le lay.sa I.out
  have mf := Square.digits_frame nw lay.mo_le lay.smo I.out
  have m0 : w32 t.mem W m=w32 s.mem W m := by simpa only [Nat.mul_zero,Nat.add_zero] using mf 0 np
  have iv : w32 t.mem W (S+16)=w32 s.mem W (S+16) := by
    have v := I.frame.val32 (d:=S+16) (k:=1) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
    simpa [val32] using v
  have ac : inputCoeff t.mem W a N k=Column.coeff (mDigits s W a) (mDigits s W a) N k :=
    Square.coeff_congr af af
  have mc : redCoeff t.mem W S m N k=
      Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k :=
    Square.coeff_congr (fun _ _ => rfl) mf
  let q := quot t.mem W a S m N k c
  let word := if k<N then q else pre t.mem W a S m N k c%2^32
  let cn := total t.mem W a S m N k c/2^32
  let residue := total t.mem W a S m N k c%2^32
  have qlt : q<2^32 := quot_lt _ _ _ _ _ _ _ _
  have qzero : N≤k → q=0 := by intro large; exact ite_eq_right (by omega)
  have small : k<N → residue=0 := by
    intro small
    exact total_cancel _ _ _ _ _ _ _ _ small (by rw [m0,iv]; exact hinv)
  have large : N≤k → residue=word%2^32 := by
    intro large
    have qz := qzero large
    change (pre t.mem W a S m N k c+q*w32 t.mem W m)%2^32=_
    rw [qz,Nat.zero_mul,Nat.add_zero]
    simp only [word,show ¬k<N by omega,ite_false,Nat.mod_mod]
  refine WP.mono (column_ok I.ws haT V lay hk nl I.bound I.carry) fun u ⟨mem,keep,edi,carry⟩ => ?_
  have qStep := qPart_memstep nw scr hk qlt qzero (by intro small; exact ite_eq_left small) mem (mDigits s W m)
  have outStep : (2^32)^N*val32 u.mem W (S+52+4*N) (k+1-N)=
      (2^32)^N*val32 t.mem W (S+52+4*N) (k-N)+(2^32)^k*residue := by
    by_cases kn : k<N
    · rw [show k+1-N=0 by omega,show k-N=0 by omega,small kn]
      simp [val32]
    · have ge : N≤k := by omega
      have v := stepMem_output t.mem W nw (by omega : S+52+4*k+4≤L) ge word cn
      rw [←mem] at v
      rw [v,large ge,←Square.pow32,Nat.mul_add,←Nat.mul_assoc,←Nat.pow_add,show N+(k-N)=k by omega]
  have carries : residue+2^32*cn=c+
      Column.coeff (mDigits s W a) (mDigits s W a) N k+
      Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k+q*mDigits s W m 0 := by
    have v := Nat.mod_add_div (total t.mem W a S m N k c) (2^32)
    change residue+2^32*cn=total t.mem W a S m N k c at v
    rw [v,total,pre,ac,mc,m0]
    rfl
  have newEq := Square.advance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I.equation carries outStep
    (Column.partSum_succ (2^32) (mDigits s W a) (mDigits s W a) N k) qStep
  have Ostep : Outside W S (12*N+56) t.mem u.mem := by rw [mem]; exact stepMem_outside _ _ nw scr hk _ _
  have Fstep : Outs W [(S+8,8),(S+52,8*N+8)] t.mem u.mem := by rw [mem]; exact stepMem_frame _ _ nw scr hk _ _
  exact ⟨I.ws.of_keeps keep,I.out.trans Ostep,I.frame.trans Fstep,I.keep.trans keep,edi,carry,
    (column_bounds (k:=k) t.mem W a S m np nl I.bound).2,newEq⟩

end VG.Proof.Mont.X86.StaticSquare
