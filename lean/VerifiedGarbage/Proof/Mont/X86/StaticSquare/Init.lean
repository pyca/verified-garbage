module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Column
public import VerifiedGarbage.Proof.Mont.X86.Rt.Save
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Saving registers, caching the inverse word and starting with zero carry -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

 theorem init_ok {s : State} {W : Addr} {L S inv : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat=W.toNat)
    (argS : (A 5).toNat=S) (argI : (A 4).toNat=inv)
    (fits : S+52≤L) (ivfit : inv+4≤L) (apart : inv+4≤S ∨ S+52≤inv) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.init) s fun t =>
      PtrAt t W .edi S ∧ SavedAt t.mem W S s.gpr ∧ Outside W S 52 s.mem t.mem ∧
      Keeps columnClob s t ∧ w32 t.mem W (S+16)=w32 s.mem W inv ∧
      w32 t.mem W (S+8)+2^32*w32 t.mem W (S+12)=0 := by
  have nw := hw.nowrap
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.init
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hw ha base argS fits) fun u ⟨pu,sv,ou,ku⟩ => ?_)
  have hu := hw.of_keeps ku
  have hau := ha.of_keeps ku (by decide)
    (Outs.of_outside (ou.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  refine WP.block_append (WP.mono (ptr_ok hau (r:=.edx) (t:=.eax) (i:=4)
    (by decide) (by decide) (by decide)) fun v ⟨pv,_,mv,kv⟩ => ?_)
  have hv := hu.of_keeps kv
  have pi : PtrAt v W .edx inv := by rw [PtrAt,pv,BitVec.toNat_add,base,argI]
  refine wp_movS (readSrc_ptr hv pi (d:=0) (by omega)) fun x X _ => ?_
  have Kx : Keeps [.eax,.edx] u x := (kv.mono (by decide)).trans (X.keeps.mono (by decide))
  have hx := hu.of_keeps Kx
  have px : PtrAt x W .edi S := by rw [PtrAt,Kx.1 .edi (by decide)]; exact pu
  have mx : x.mem=u.mem := X.mem.trans mv
  have invValue : x.gpr .eax=u.mem.readW (off W inv) 32 := by rw [X.gpr,mv,Nat.add_zero]
  refine wp_storeS (ea_ptr hx px (by omega)) (ws_write hx (by omega)) fun y Y => wp_movS rfl fun z Z _ => ?_
  have Kz : Keeps [.eax,.edx] u z := (Kx.trans (Y.keeps _)).trans (Z.keeps.mono (by decide))
  have hz := hu.of_keeps Kz
  have pz : PtrAt z W .edi S := by rw [PtrAt,Kz.1 .edi (by decide)]; exact pu
  refine wp_storeS (ea_ptr hz pz (by omega)) (ws_write hz (by omega)) fun r R => ?_
  have hr := hz.of_keeps (R.keeps [])
  have pr : PtrAt r W .edi S := by rw [PtrAt,R.gpr]; exact pz
  refine wp_storeS (ea_ptr hr pr (by omega)) (ws_write hr (by omega)) fun t T => WP.block_nil ?_
  have mt : t.mem=((u.mem.writeW (off W (S+16)) (u.mem.readW (off W inv) 32)).writeW
      (off W (S+8)) (0#32)).writeW (off W (S+12)) (0#32) := by
    rw [T.mem,R.mem,Z.mem,Y.mem,mx,invValue,R.gpr,Z.gpr]
    rfl
  have oi : Outside W (S+16) 4 u.mem (u.mem.writeW (off W (S+16)) (u.mem.readW (off W inv) 32)) :=
    writeW32_outside _ _ _ (by omega)
  have o8 := writeW32_outside (u.mem.writeW (off W (S+16)) (u.mem.readW (off W inv) 32)) W
    (d:=S+8) (0#32) (by omega : S+8+4≤2^64)
  have o12 := writeW32_outside ((u.mem.writeW (off W (S+16)) (u.mem.readW (off W inv) 32)).writeW
    (off W (S+8)) (0#32)) W (d:=S+12) (0#32) (by omega : S+12+4≤2^64)
  have tail : Outside W (S+8) 12 u.mem t.mem := by
    rw [mt]
    exact ((oi.mono (by omega) (by omega)).trans (o8.mono (by omega) (by omega))).trans
      (o12.mono (by omega) (by omega))
  have Kt : Keeps [.eax,.edx] u t := Kz.trans ((R.keeps _).trans (T.keeps _))
  refine ⟨?_,?_,?_,(ku.mono (by decide)).trans (Kt.mono (by decide)),?_,?_⟩
  · rw [PtrAt,Kt.1 .edi (by decide)]
    exact pu
  · exact sv.of_outs (Outs.of_outside (rs:=[(S+8,12)]) tail (by simp))
      (by intro r hr; rw [List.mem_singleton.mp hr]; dsimp only; omega) (by omega)
  · exact (ou.mono (by omega) (by omega)).trans (tail.mono (by omega) (by omega))
  · rw [mt,o12.w32 (by omega) (by omega),o8.w32 (by omega) (by omega),w32_write_self]
    exact ou.w32 (by omega) (by omega)
  · rw [mt,o12.w32 (by omega) (by omega),w32_write_self,w32_write_self]
    rfl

end VG.Proof.Mont.X86.StaticSquare
