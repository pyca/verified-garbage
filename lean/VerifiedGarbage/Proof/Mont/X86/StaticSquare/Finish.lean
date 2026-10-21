module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Column
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Storing the final carry above the square's high half -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

 theorem finish_ok {s : State} {W : Addr} {L S N c : Nat}
    (hw : Ws s W L) (ps : PtrAt s W .edi S) (fits : S+52+8*N+8≤L)
    (carry : w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12)=c) (cc : c<2^32) :
    WP isa (.block (VG.Impl.Mont.X86.Rt.StaticSquare.finish N)) s fun t =>
      Outside W (S+52+8*N) 8 s.mem t.mem ∧ PtrAt t W .ebp (S+52+4*N) ∧
      val32 t.mem W (S+52+4*N) (N+1)=val32 s.mem W (S+52+4*N) N+(2^32)^N*c ∧
      Keeps [.eax,.ebp] s t := by
  have nw := hw.nowrap
  have low : s.mem.readW (off W (S+8)) 32=BitVec.ofNat 32 c := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt cc]
    change w32 s.mem W (S+8)=c
    omega
  have high : w32 s.mem W (S+12)=0 := by omega
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.finish
  refine wp_movS rfl fun u U _ => wp_addS rfl fun v V _ => ?_
  have KV : Keeps [.ebp] s v := U.keeps.trans V.keeps
  have mv : v.mem=s.mem := V.mem.trans U.mem
  have pv : PtrAt v W .ebp (S+52+8*N) := by
    rw [PtrAt,V.gpr,U.gpr]
    have e := ptr_add ps (BitVec.ofNat 32 (52+8*N))
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 52+8*N<2^32),Nat.add_assoc] using e
  have pvs : PtrAt v W .edi S := by rw [PtrAt,KV.1 .edi (by decide)]; exact ps
  have hv := hw.of_keeps KV
  refine wp_movS (readSrc_ptr hv pvs (d:=8) (by omega)) fun x X _ => ?_
  have px : PtrAt x W .ebp (S+52+8*N) := by rw [PtrAt,X.other .ebp (by decide)]; exact pv
  have hx := hv.of_keeps X.keeps
  refine wp_storeS (ea_ptr hx px (d:=0) (by omega)) (ws_write hx (by omega)) fun y Y => ?_
  have KY : Keeps [.eax,.ebp] s y :=
    ((KV.mono (by decide)).trans (X.keeps.mono (by decide))).trans (Y.keeps _)
  have hy := hw.of_keeps KY
  have pys : PtrAt y W .edi S := by rw [PtrAt,KY.1 .edi (by decide)]; exact ps
  have my : y.mem=s.mem.writeW (off W (S+52+8*N)) (BitVec.ofNat 32 c) := by
    rw [Y.mem,X.mem,mv,X.gpr,mv,low,Nat.add_zero]
  have O1 := writeW32_outside s.mem W (d:=S+52+8*N) (BitVec.ofNat 32 c)
    (by omega : S+52+8*N+4≤2^64)
  have highY : y.mem.readW (off W (S+12)) 32=0#32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 y.mem W (S+12)=0
    rw [my,O1.w32 (by omega) (by omega),high]
  refine wp_movS (readSrc_ptr hy pys (d:=12) (by omega)) fun z Z _ => ?_
  have KZ : Keeps [.eax,.ebp] s z := KY.trans (Z.keeps.mono (by decide))
  have hz := hw.of_keeps KZ
  have pz : PtrAt z W .ebp (S+52+8*N) := by rw [PtrAt,Z.other .ebp (by decide),Y.gpr]; exact px
  refine wp_storeS (ea_ptr hz pz (d:=4) (by omega)) (ws_write hz (by omega)) fun r R => wp_subS rfl fun t T _ => WP.block_nil ?_
  have mt : t.mem=(s.mem.writeW (off W (S+52+8*N)) (BitVec.ofNat 32 c)).writeW
      (off W (S+52+8*N+4)) (0#32) := by
    rw [T.mem,R.mem,Z.mem,my,Z.gpr,highY]
  have O2 := writeW32_outside (s.mem.writeW (off W (S+52+8*N)) (BitVec.ofNat 32 c)) W
    (d:=S+52+8*N+4) (0#32) (by omega : S+52+8*N+4+4≤2^64)
  have Ot : Outside W (S+52+8*N) 8 s.mem t.mem := by
    rw [mt]
    exact (O1.mono (by omega) (by omega)).trans (O2.mono (by omega) (by omega))
  have K : Keeps [.eax,.ebp] s t :=
    (KZ.trans (R.keeps _)).trans (T.keeps.mono (by decide))
  refine ⟨Ot,?_,?_,K⟩
  · rw [PtrAt,T.gpr]
    have pr : PtrAt r W .ebp (S+52+8*N) := by rw [PtrAt,R.gpr]; exact pz
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*N<2^32),
      show S+52+8*N-4*N=S+52+4*N by omega] using
      ptr_sub pr (BitVec.ofNat 32 (4*N)) (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*N<2^32)]; omega)
  · rw [val32_succ,Ot.val32 (by omega) (by omega),show S+52+4*N+4*N=S+52+8*N by omega,mt,
      O2.w32 (by omega) (by omega),w32_write_self,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cc,Square.pow32]

end VG.Proof.Mont.X86.StaticSquare
