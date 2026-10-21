module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.Columns
import VerifiedGarbage.Proof.Mont.X86.Rt.Front
public import VerifiedGarbage.Proof.Mont.X86.Rt.Save
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem front_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S m inv o a : Nat} (V : ArgVals A W N S m inv o a a) (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a)
    (np : 0<N) (hinv : (val32 s.mem W m N*w32 s.mem W inv+1)%2^32=0)
    (hlt : val32 s.mem W a N<val32 s.mem W m N) :
    WP isa (.seq (.block save) VG.Impl.Mont.X86.Rt.Square.columns) s fun t =>
      Outs W [(S,12*N+56)] s.mem t.mem ∧ SavedAt t.mem W S s.gpr ∧ PtrAt t W .ebp (S+accOff+4*N) ∧
      val32 t.mem W (S+accOff+4*N) (N+1)<2*val32 s.mem W m N ∧
      (∃ q,2^(32*N)*val32 t.mem W (S+accOff+4*N) (N+1)=
        val32 s.mem W a N*val32 s.mem W a N+q*val32 s.mem W m N) ∧
      t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have nw := hw.nowrap
  have scr := lay.scr
  refine WP.seq (WP.mono (save_ok hw ha V.ws V.s (by omega)) fun s1 ⟨edi1,sv1,O1,K1⟩ => ?_)
  have O1' : Outside W S (12*N+56) s.mem s1.mem := O1.mono (by omega) (by omega)
  have ha1 := ha.of_keeps K1 (by decide)
    (Outs.of_outside (O1'.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  have hw1 := hw.of_keeps K1
  have mv1 : val32 s1.mem W m N=val32 s.mem W m N := O1'.val32 lay.smo (by have := lay.mo_le;omega)
  have av1 : val32 s1.mem W a N=val32 s.mem W a N := O1'.val32 lay.sa (by have := lay.a_le;omega)
  have iv1 : w32 s1.mem W inv=w32 s.mem W inv := O1'.w32 lay.sinv (by have := lay.inv_le;omega)
  have low : (w32 s1.mem W m*w32 s1.mem W inv+1)%2^32=0 :=
    low_inverse _ _ _ _ np (by rw [mv1,iv1];exact hinv)
  refine WP.mono (columns_ok ha1 hw1 V lay np edi1 low (by rw [av1,mv1];exact hlt))
    fun t ⟨O2,F2,bp2,lt2,⟨q,e2⟩,K2⟩ => ?_
  have allK : Keeps [.eax,.edx,.edi,.ecx,.ebp,.ebx,.esi] s t :=
    (K1.mono (by decide)).trans (K2.mono (by decide))
  refine ⟨Outs.of_outside (O1'.trans O2) (List.mem_singleton_self _),?_,?_,?_,?_,
    allK.1 _ (by decide),allK.2.1,allK.2.2⟩
  · exact sv1.of_outs F2 (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp only <;> omega) (by omega)
  · simpa only [accOff_eq] using bp2
  · simpa only [accOff_eq,mv1] using lt2
  · refine ⟨q,?_⟩
    simpa only [accOff_eq,pow32,av1,mv1] using e2

end VG.Proof.Mont.X86.Square
