module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Omega

/-! Rebase arithmetic write footprints to the point workspace. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64.Mont (ofs_off_sub off_off wordsVal_off)

theorem outside_rebase {base : Addr} {e o n : Nat} {m m' : Mem}
    (h : Outside (off base e) o n m m') (he : e+o+n<2^64) : Outside base (e+o) n m m' := by
  intro x hx
  apply h x
  rw [ofs_off_sub base x e (by omega_arith)]
  have klt : ofs base x<2^64 := (x-base).isLt
  by_cases hk : ofs base x<e
  · right
    rw [Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [show 2^64-e+ofs base x=(ofs base x-e)+2^64 by omega_arith,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem stable_input_apart {s : VG.AArch64.State} {base : Addr} {a o : Nat}
    (apart : a+72≤o ∨ o+64≤a) (fitsA : a+72≤2^64) (fitsO : o+64<2^64) :
    StableInput s (off base a) (off base o) := by
  intro m outside d hd
  have h := outside_rebase outside (by simpa only [Nat.add_zero] using fitsO)
  have hw := h.word (d:=a+d) (by omega_arith) (by omega_arith)
  simpa only [word,off_off] using hw

end VG.Proof.Mont.AArch64.P521Field
