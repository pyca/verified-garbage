import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
import VerifiedGarbage.Proof.P256.Linear.Linear41
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M Sl layout aligned)

section
variable {m : Nat} [NeZero m] {R : Nat}
theorem toM_mod (x : Nat) : toM m R (x%m)=toM m R x := by
  unfold toM; rw [ofNat_mod]

theorem toM_scale (c x : Nat) : toM m R (c*x)=Fin.ofNat m c*toM m R x := by
  unfold toM
  rw [ofNat_mul']
  grind

theorem toM_linear (a b c d : Nat) (hb : b<m) :
    toM m R ((c*a+d*(m-b))%m)=
      Fin.ofNat m c*toM m R a-Fin.ofNat m d*toM m R b := by
  rw [toM_add,toM_scale,toM_scale]
  have h : toM m R (m-b)= -toM m R b := by
    have hh := toM_sub (m:=m) (R:=R) (A:=0) (B:=b) (by omega)
    simp only [Nat.zero_add,toM_mod,toM_zero] at hh
    grind
  rw [h]
  grind

theorem toM_linear41 (a b : Nat) (hb : b<m) :
    toM m R ((4*a+m-b)%m)=4*toM m R a-toM m R b := by
  rw [toM_sub (by omega),toM_scale]
  rfl
end

theorem linearKeep {base : Addr} {o : Nat} {s t : State}
    (hk : KeepRegs (clob 4) s t) (ho : Outside base o 32 s.mem t.mem) : OpKeep M base o s t :=
  ⟨hk.gpr,hk.rd,hk.wr,hk.sp,fun x hx _ => ho x hx⟩

theorem inv_keep_unused {base : Addr} {o : Nat} {s t : State} {V : List Nat} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl V E s) (ho : Sl o) (hv : o∉V) (hk : OpKeep M base o s t) :
    Inv M base 8192 C.p Sl V E t := by
  have hg : ProgKeep M base [o] s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp,fun x hx ht => hk.mem x (hx o (by simp)) ht⟩
  have he (x : Nat) (hx : x∈V) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
    exact opKeep_wordsVal hk (layout.apart x o (hi.sl x hx) ho (by intro h; subst x; exact hv hx))
      (layout.tmp x (hi.sl x hx)) (by have := layout.le x (hi.sl x hx); omega)
  refine ⟨hg.scr hi.scr,?_,hi.sl,fun x hx => by rw [he x hx]; exact hi.lt x hx,
    fun x hx => by rw [he x hx]; exact hi.val x hx⟩
  have hm := hi.mod
  refine ⟨hm.n0,hm.n10,hm.mo,hm.tmp,hm.sep,?_,hm.inv,hm.red,hm.call⟩
  rw [opKeep_wordsVal hk (layout.mo o ho).symm hm.sep (by have := hm.mo; omega)]
  exact hm.val
end VG.Proof.P256.EcdhDouble
