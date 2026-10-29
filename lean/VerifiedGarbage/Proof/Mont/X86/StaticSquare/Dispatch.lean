module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint

import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Body
import VerifiedGarbage.Proof.Mont.X86.Square.Body
import VerifiedGarbage.Proof.Framework.PlainSimp

-- Formerly `VerifiedGarbage/Proof/Mont/X86/StaticSquare/SelectSize.lean`, which only this module imported.
section

/-! # Selecting a proved square using only its public limb count -/

section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

 def SquarePost (W : Addr) (S N mo o a : Nat) (s t : State) : Prop :=
  Outs W [(S,12*N+56),(o,4*N)] s.mem t.mem ∧ val32 t.mem W o N<val32 s.mem W mo N ∧
  val32 t.mem W o N*2^(32*N)%val32 s.mem W mo N=val32 s.mem W a N*val32 s.mem W a N%val32 s.mem W mo N ∧
  t.gpr .ebx=s.gpr .ebx ∧ t.gpr .esi=s.gpr .esi ∧ t.gpr .ebp=s.gpr .ebp ∧ t.gpr .edi=s.gpr .edi ∧
  t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr

 theorem selectSize_ok {W : Addr} {L N S mo inv o a K : Nat} {A : Nat → BitVec 32} {fallback : Prog isa}
    (V : ArgVals A W N S mo inv o a a) (lay : VG.Proof.Mont.X86.Rt.Lay L N S mo inv a a)
    (np : 0<N) (n32 : 4*N<2^32) (ol : o+4*N≤L) (so : o+4*N≤S ∨ S+12*N+56≤o)
    (kp : 0<K) (kl : K≤128) (even : K%2=0)
    (other : ∀ u, Ws u W L → Args u W L A →
      (val32 u.mem W mo N*w32 u.mem W inv+1)%2^32=0 → val32 u.mem W a N<val32 u.mem W mo N →
      WP isa fallback u (SquarePost W S N mo o a u))
    (s : State) (hw : Ws s W L) (ha : Args s W L A)
    (hinv : (val32 s.mem W mo N*w32 s.mem W inv+1)%2^32=0)
    (hb : val32 s.mem W a N<val32 s.mem W mo N) :
    WP isa (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize K fallback) s (SquarePost W S N mo o a s) := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.selectSize
  refine WP.seq (wp_movS (ha.read 2 (by decide)) fun u U _ => wp_cmpS rfl fun v F zf => WP.block_nil ?_)
  have Kkeep : Keeps [.eax] s v := U.keeps.trans (F.keeps _)
  have mem : v.mem=s.mem := F.mem.trans U.mem
  have hav := ha.of_keeps Kkeep (by decide) (by rw [mem]; exact Outs.refl _ _ _)
  have hwv := hw.of_keeps Kkeep
  have z : v.zf=some (A 2-BitVec.ofNat 32 (K/2)==0) := by rw [zf,U.gpr]
  have finish : ∀ c, WP isa c v (SquarePost W S N mo o a v) → WP isa c v (SquarePost W S N mo o a s) := by
    intro c hc
    refine WP.mono hc fun t ⟨O,lt,eq,bx,si,bp,di,sp,rd,wr⟩ => ?_
    rw [mem] at O lt eq
    exact ⟨O,lt,eq,bx.trans (Kkeep.1 _ (by decide)),si.trans (Kkeep.1 _ (by decide)),
      bp.trans (Kkeep.1 _ (by decide)),di.trans (Kkeep.1 _ (by decide)),sp.trans (Kkeep.1 _ (by decide)),
      rd.trans Kkeep.2.1,wr.trans Kkeep.2.2⟩
  refine WP.ite (A 2-BitVec.ofNat 32 (K/2)==0) (by exact z) ?_ ?_
  · intro yes
    have e : A 2=BitVec.ofNat 32 (K/2) := by
      have zero : A 2-BitVec.ofNat 32 (K/2)=0 := by simpa only [beq_iff_eq] using yes
      exact by simpa using BitVec.sub_eq_iff_eq_add.mp zero
    have eN : N=K := by
      have vn := V.n
      rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : K/2<2^32)] at vn
      omega
    subst K
    exact finish _ (square_ok hwv hav V lay np kl n32 ol so (by rw [mem]; exact hinv) (by rw [mem]; exact hb))
  · intro _
    exact finish _ (other v hwv hav (by rw [mem]; exact hinv) (by rw [mem]; exact hb))

 theorem selectAll_ok {s : State} {W : Addr} {L N S mo inv o a : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (V : ArgVals A W N S mo inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S mo inv a a)
    (np : 0<N) (n32 : 4*N<2^32) (ol : o+4*N≤L) (so : o+4*N≤S ∨ S+12*N+56≤o)
    (hinv : (val32 s.mem W mo N*w32 s.mem W inv+1)%2^32=0)
    (hb : val32 s.mem W a N<val32 s.mem W mo N) :
    WP isa (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize 32
      (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize 48
      (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize 64
      (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize 96
        (VG.Impl.Mont.X86.Rt.StaticSquare.selectSize 128 VG.Impl.Mont.X86.Rt.Square.square))))) s
      (SquarePost W S N mo o a s) := by
  apply selectSize_ok V lay np n32 ol so (by decide) (by decide) (by decide) _ s hw ha hinv hb
  intro s hw ha hinv hb
  apply selectSize_ok V lay np n32 ol so (by decide) (by decide) (by decide) _ s hw ha hinv hb
  intro s hw ha hinv hb
  apply selectSize_ok V lay np n32 ol so (by decide) (by decide) (by decide) _ s hw ha hinv hb
  intro u hu hau iu bu
  apply selectSize_ok V lay np n32 ol so (by decide) (by decide) (by decide) _ u hu hau iu bu
  intro v hv hav iv bv
  apply selectSize_ok V lay np n32 ol so (by decide) (by decide) (by decide) _ v hv hav iv bv
  intro t ht hat it bt
  exact Square.square_ok ht hat V lay np n32 ol so it bt

end VG.Proof.Mont.X86.StaticSquare
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem dispatch_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (lay : VG.Proof.Mont.X86.Rt.Lay L N S mo inv a b)
    (np : 0<N) (n32 : 4*N<2^32) (ol : o+4*N≤L) (so : o+4*N≤S ∨ S+12*N+56≤o)
    (hinv : (val32 s.mem W mo N*w32 s.mem W inv+1)%2^32=0)
    (hb : val32 s.mem W b N<val32 s.mem W mo N) :
    WP isa VG.Impl.Mont.X86.Rt.StaticSquare.dispatch s fun t =>
      Outs W [(S,12*N+56),(o,4*N)] s.mem t.mem ∧ val32 t.mem W o N<val32 s.mem W mo N ∧
      val32 t.mem W o N*2^(32*N)%val32 s.mem W mo N=val32 s.mem W a N*val32 s.mem W b N%val32 s.mem W mo N ∧
      t.gpr .ebx=s.gpr .ebx ∧ t.gpr .esi=s.gpr .esi ∧ t.gpr .ebp=s.gpr .ebp ∧ t.gpr .edi=s.gpr .edi ∧
      t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.dispatch
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
    refine WP.mono (selectAll_ok ws3 ha3 V lay np n32 ol so (by rw [mem];exact hinv) (by rw [mem];exact hb))
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

end VG.Proof.Mont.X86.StaticSquare
