module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
import VerifiedGarbage.Proof.Mont.X86.Rt.Body
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem dispatch_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (lay : VG.Proof.Mont.X86.Rt.Lay L N S mo inv a b)
    (np : 0<N) (n32 : 4*N<2^32) (ol : o+4*N≤L) (so : o+4*N≤S ∨ S+12*N+56≤o)
    (hinv : (val32 s.mem W mo N*w32 s.mem W inv+1)%2^32=0)
    (hb : val32 s.mem W b N<val32 s.mem W mo N) :
    WP isa VG.Impl.Mont.X86.Rt.Square.dispatch s fun t =>
      Outs W [(S,12*N+56),(o,4*N)] s.mem t.mem ∧ val32 t.mem W o N<val32 s.mem W mo N ∧
      val32 t.mem W o N*2^(32*N)%val32 s.mem W mo N=val32 s.mem W a N*val32 s.mem W b N%val32 s.mem W mo N ∧
      t.gpr .ebx=s.gpr .ebx ∧ t.gpr .esi=s.gpr .esi ∧ t.gpr .ebp=s.gpr .ebp ∧ t.gpr .edi=s.gpr .edi ∧
      t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  unfold VG.Impl.Mont.X86.Rt.Square.dispatch
  apply WP.seq
  refine wp_movS (ha.read 7 (by decide)) fun t1 u1 _ => ?_
  have ha1 := ha.of_upd u1 (by decide)
  refine wp_movS (ha1.read 8 (by decide)) fun t2 u2 _ => wp_cmpS rfl fun t3 f3 zf => WP.block_nil ?_
  have K : Keeps [.eax,.edx] s t3 :=
    (u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans (f3.keeps _))
  have mem : t3.mem=s.mem := f3.mem.trans (u2.mem.trans u1.mem)
  have ha3 := ha.of_keeps K (by decide) (by rw [mem];exact Outs.refl _ _ _)
  have ws3 := hw.of_keeps K
  have zf3 : t3.zf=some (A 7-A 8==0) := by rw [zf,u2.other _ (by decide),u1.gpr,u2.gpr]
  refine WP.ite (A 7-A 8==0) (by change t3.zf=_;exact zf3) ?_ ?_
  · intro yes
    have e : A 7=A 8 := by
      have zero : A 7-A 8=0 := by simpa only [beq_iff_eq] using yes
      have eq := BitVec.sub_eq_iff_eq_add.mp zero
      simpa using eq
    have ab : a=b := by rw [← V.a,← V.b,e]
    subst b
    refine WP.mono (square_ok ws3 ha3 V lay np n32 ol so (by rw [mem];exact hinv) (by rw [mem];exact hb))
      fun t ⟨O,lt,eq,bx,si,bp,di,sp,rd,wr⟩ => ?_
    rw [mem] at O lt eq
    exact ⟨O,lt,eq,bx.trans (K.1 _ (by decide)),si.trans (K.1 _ (by decide)),bp.trans (K.1 _ (by decide)),
      di.trans (K.1 _ (by decide)),sp.trans (K.1 _ (by decide)),rd.trans K.2.1,wr.trans K.2.2⟩
  · intro _
    refine WP.mono (VG.Proof.Mont.X86.Rt.scalarBody_ok ws3 ha3 V lay np n32 ol so
      (by rw [mem];exact hinv) (by rw [mem];exact hb)) fun t ⟨O,lt,eq,bx,si,bp,di,sp,rd,wr⟩ => ?_
    rw [mem] at O lt eq
    exact ⟨O,lt,eq,bx.trans (K.1 _ (by decide)),si.trans (K.1 _ (by decide)),bp.trans (K.1 _ (by decide)),
      di.trans (K.1 _ (by decide)),sp.trans (K.1 _ (by decide)),rd.trans K.2.1,wr.trans K.2.2⟩

end VG.Proof.Mont.X86.Square
