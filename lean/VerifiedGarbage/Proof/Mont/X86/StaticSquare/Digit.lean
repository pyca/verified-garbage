module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Product
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum

/-! # Writing a quotient digit and cancelling its low product word -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.StaticSquare

 theorem value_low (s : State) : value s%2^32=(s.gpr .esi).toNat := by
  have := (s.gpr .esi).isLt
  dsimp only [value]
  omega

 theorem value_high (s : State) : value s/2^32=(s.gpr .ebx).toNat+2^32*(s.gpr .ecx).toNat := by
  have := (s.gpr .esi).isLt
  dsimp only [value]
  omega

 theorem digit_ok {s : State} {W : Addr} {L S m N k : Nat}
    (hw : Ws s W L) (ps : PtrAt s W .edi S) (pm : PtrAt s W .ebp m)
    (fits : S+52+4*k+4≤L) (mf : m+4≤L)
    (apart : m+4≤S ∨ S+52+4*k+4≤m)
    (bound : value s+(if k<N then ((s.gpr .esi).toNat*w32 s.mem W (S+16))%2^32 else 0)*w32 s.mem W m<2^96) :
    let q := if k<N then ((s.gpr .esi).toNat*w32 s.mem W (S+16))%2^32 else 0
    let d := if k<N then q else (s.gpr .esi).toNat
    WP isa (.block (digit N k)) s fun t =>
      value t=value s+q*w32 s.mem W m ∧
      Keeps [.eax,.edx,.esi,.ebx,.ecx] s t ∧
      t.mem=s.mem.writeW (off W (S+(52+4*k))) (BitVec.ofNat 32 d) := by
  intro q d
  unfold digit
  split
  · next small =>
    have qe : q=((s.gpr .esi).toNat*w32 s.mem W (S+16))%2^32 := ite_eq_left small
    have de : d=q := ite_eq_left small
    have ql : q<2^32 := by rw [qe]; exact Nat.mod_lt _ (by decide)
    simp only [List.cons_append,List.nil_append]
    refine wp_movS rfl fun u U _ => ?_
    have hu := hw.of_keeps U.keeps
    have pu : PtrAt u W .edi S := by rw [PtrAt,U.other .edi (by decide)]; exact ps
    refine wp_movS (readSrc_ptr hu pu (by omega)) fun v V _ => wp_mul fun x X => ?_
    have K : Keeps [.eax,.edx] s x :=
      ((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))).trans X.keeps
    have memX : x.mem=s.mem := X.mem.trans (V.mem.trans U.mem)
    have qx : x.gpr .eax=BitVec.ofNat 32 q := by
      rw [X.eax,V.other .eax (by decide),U.gpr,V.gpr,U.mem,qe]
      exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat,Nat.mod_mod])
    have px : PtrAt x W .edi S := by rw [PtrAt,K.1 .edi (by decide)]; exact ps
    have hx := hw.of_keeps K
    refine wp_storeS (ea_ptr hx px (by omega)) (ws_write hx (by omega)) fun y Y => ?_
    have KY : Keeps [.eax,.edx] s y := K.trans (Y.keeps _)
    have memY : y.mem=s.mem.writeW (off W (S+(52+4*k))) (BitVec.ofNat 32 q) := by
      rw [Y.mem,memX,qx]
    have hy := hw.of_keeps KY
    have py : PtrAt y W .ebp m := by rw [PtrAt,KY.1 .ebp (by decide)]; exact pm
    have mY : w32 y.mem W m=w32 s.mem W m := by
      rw [memY]
      exact (writeW32_outside s.mem W (d:=S+(52+4*k)) (BitVec.ofNat 32 q)
        (by have := hw.nowrap; omega)).w32 (by omega) (by have := hw.nowrap; omega)
    refine wp_movS (readSrc_ptr hy py (d:=0) (by omega)) fun z Z _ => wp_mul fun a M => ?_
    have KA : Keeps [.eax,.edx] s a :=
      (KY.trans (Z.keeps.mono (by decide))).trans M.keeps
    have prod : (a.gpr .eax).toNat+2^32*(a.gpr .edx).toNat=q*w32 s.mem W m := by
      rw [M.eax,M.edx,Z.other .eax (by decide),Y.gpr,qx,Z.gpr]
      have e := (mul_words (BitVec.ofNat 32 q) (y.mem.readW (off W (m+0)) 32)).1
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ql,Nat.add_zero] at e
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ql,Nat.add_zero] using
        e.trans (congrArg (q*·) mY)
    have ba : value a+(a.gpr .eax).toNat+2^32*(a.gpr .edx).toNat<2^96 := by
      rw [value_keeps KA,Nat.add_assoc,prod]
      exact bound
    refine WP.mono (accum_ok a ba) fun t ⟨vt,kt,mt⟩ => ⟨?_,?_,?_⟩
    · rw [vt,value_keeps KA,Nat.add_assoc,prod]
    · exact (KA.mono (by decide)).trans (kt.mono (by decide))
    · rw [mt,M.mem,Z.mem,memY,de]
  · next large =>
    have qe : q=0 := ite_eq_right large
    have de : d=(s.gpr .esi).toNat := ite_eq_right large
    refine wp_storeS (ea_ptr hw ps (by omega)) (ws_write hw (by omega)) fun t T => WP.block_nil ?_
    refine ⟨?_,T.keeps _,?_⟩
    · simp only [value,T.gpr,qe,Nat.zero_mul,Nat.add_zero]
    · rw [T.mem,de]
      congr 1
      exact (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (s.gpr .esi).isLt])).symm

end VG.Proof.Mont.X86.StaticSquare
