module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Layout
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.AbHalf
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Half
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Signed value rows and reduced coefficient rows at the prime width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 theorem fgRow_ok {s : State} {base : Addr} {size w n p row : Nat} {u v f g : Int}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size) (hr : row<2)
    (hu : s.mem.readW (VG.Proof.Mont.off base (offset w 3+12+8*row)) 32=BitVec.ofInt 32 u)
    (hv : s.mem.readW (VG.Proof.Mont.off base (offset w 3+16+8*row)) 32=BitVec.ofInt 32 v)
    (huv : |u|+|v|≤2^30)
    (hf : (val32 s.mem base (offset w 4) (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1)))
    (hg : (val32 s.mem base (offset w 5) (n+1) : Int)%2^(32*(n+1))=g%2^(32*(n+1)))
    (hfb : |f|≤p) (hgb : |g|≤p) (hp : p<2^(32*n+1)) (hdiv : 2^30∣u*f+v*g) :
    WP isa (.block (VG.Impl.Weierstrass.X86.Inv.linear (offset w 3+12+8*row) (offset w 3+16+8*row)
      (offset w 11) (offset w 4) (offset w 5) (offset w 12) (n+1) (n-1)++
      VG.Impl.Weierstrass.X86.Inv.shr30 (offset w row) (offset w 11) (n+1))) s fun z =>
      (val32 z.mem base (offset w row) (n+1) : Int)%2^(32*(n+1))=((u*f+v*g)/2^30)%2^(32*(n+1)) ∧
      Keeps clob s z ∧ Unch base [(offset w 11,4*(n+3)),(offset w 12,4*n),(offset w row,4*(n+1))] s.mem z.mem := by
  have e : n-1+2=n+1 := by omega
  have e1 : n-1+1=n := by omega
  have H := GcdBatch.half_wide_ok (k:=n-1) (p:=p) (dst:=offset w row) hs
    (by simpa only [e] using fg_layout hn hw hz row hr)
    (by rcases (show row=0 ∨ row=1 by omega) with rfl | rfl <;> dsimp only [offset] at * <;> omega)
    (by rcases (show row=0 ∨ row=1 by omega) with rfl | rfl <;> dsimp only [offset] at * <;> omega)
    hu hv huv (by simpa only [e] using hf) (by simpa only [e] using hg) hfb hgb
    (by simpa only [e1] using hp) hdiv
  simpa only [e,e1,show n+1+2=n+3 by omega] using H

 theorem abRow_ok {s : State} {base : Addr} {size w n p iv row : Nat} {u v a b : Int}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0)
    (hz : offset w 15≤size) (hr : row<2)
    (hi : iv<2^32) (hiv : w32 s.mem base (offset w 3+28)=iv)
    (hp : 0<p) (hm : val32 s.mem base (offset w 2) n=p) (hinv : (p*iv+1)%2^32=0)
    (hu : s.mem.readW (VG.Proof.Mont.off base (offset w 3+12+8*row)) 32=BitVec.ofInt 32 u)
    (hv : s.mem.readW (VG.Proof.Mont.off base (offset w 3+16+8*row)) 32=BitVec.ofInt 32 v)
    (huv : |u|+|v|≤2^30)
    (ha : (val32 s.mem base (offset w 6) n : Int)=a) (hb : (val32 s.mem base (offset w 7) n : Int)=b)
    (hab : |a|≤p) (hbb : |b|≤p) :
    WP isa (.block (VG.Impl.Weierstrass.X86.Inv.linear (offset w 3+12+8*row) (offset w 3+16+8*row)
      (offset w 11) (offset w 6) (offset w 7) (offset w 12) n (n-1)++
      VG.Impl.Rsa.X86.InvBatch.reduce w n (offset w (13+row)))) s fun z =>
      (val32 z.mem base (offset w (13+row)) n : Int)=VG.Proof.Divstep.W32.mred p iv (u*a+v*b) ∧
      Keeps wordClob s z ∧ Unch base [(offset w 11,4*(n+2)),(offset w 12,4*(n+1)),
        (offset w 12,4*n),(offset w (13+row),4*n)] s.mem z.mem := by
  have e : n-1+1=n := by omega
  have mi : (minv32 (model w n iv)).toNat=iv := by
    change ((BitVec.ofNat 64 iv).setWidth 32).toNat=iv
    rw [BitVec.setWidth_ofNat_of_le (by decide),BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi]
  rw [reduce_eq w n (offset w (13+row)) iv]
  have H := abHalfLoaded_ok (k:=n-1) (M:=model w n iv) (iv:=offset w 3+28) hs
    (by simpa only [e] using ab_layout hn hw hz row hr)
    (by simpa only [e] using red_layout hn hw he hz row hr)
    (by dsimp only [offset] at *; omega)
    (by dsimp only [offset] at *; omega) (by dsimp only [offset] at *; omega)
    (by rw [mi]; exact hiv) hp (by simpa only [e,model] using hm)
    (by rw [mi]; exact hinv) hu hv huv (by simpa only [e] using ha) (by simpa only [e] using hb) hab hbb
  rw [mi] at H
  simpa only [e,model] using H

end VG.Proof.Rsa.X86.InvBatch
