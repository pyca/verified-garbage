import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic

/-!
# P-256 on x86-64: the Jacobian window method with the doubling by halving

The doubling by halving (`doubleHalfPublic`, `doubleHalfPublic_ok`) is a
doubling the Jacobian window method can use (`doubleHalfPublic_dblOk`), and
P-256's order is `17 (mod 32)` (`n_mod32`), so `winJac_ok` gives `[k]P` for
`k < n` (`winJacP256_ok`).
-/

namespace VG.Proof.P256.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

/-- The doubling by halving doubles a Jacobian triple in place. -/
theorem doubleHalfPublic_dblOk {M : Mod} {S : RcbSlots} (hn : M.n = 4)
    (hm : UnitMod Spec.P256.p (2 ^ (64 * M.n))) (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) :
    DblOk M S Spec.P256.curve (doubleHalfPublic M S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  have hsub : (doubleSlots S p).Sublist (rcbW S p) :=
    .cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.refl _))))))
  refine WP.mono (doubleHalfPublic_ok hn hL hm hC ha (hnd.sublist hsub) (fun x hx => hSl x (hsub.subset hx))
    hI (fun x hx => hx) hQ hJ) fun t ⟨k, I, J⟩ =>
    ⟨k.mono fun x hx => hsub.subset hx, _, I.sub fun x hx => List.mem_append_left _ hx, J⟩

/-- P-256's order is `17` modulo `32`. -/
theorem n_mod32 : Spec.P256.curve.n % 32 = 17 := by decide

theorem n_ge64 : 64 ≤ Spec.P256.curve.n := by decide

/-- `[k]P` into `R` by the Jacobian window method with the doubling by halving,
if `k < n`, on P-256. -/
theorem winJacP256_ok {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size)
    (hp : UnitMod Spec.P256.p (2 ^ (64 * K.M.n))) (hC : Law Spec.P256.curve) (hM3 : AM3 Spec.P256.curve)
    (hO : PrimeOrder Spec.P256.curve) (hpn : Spec.P256.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < Spec.P256.p)
    (hone : toM Spec.P256.p (2 ^ (64 * K.M.n)) K.one = 1) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P = true) {k : Nat}
    (hkJ : k + JacWinCfg.offset K.J < 32 ^ K.J) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size Spec.P256.p s.mem base) (hF : JacWinFixed K Spec.P256.curve base s P k) :
    WP isa (K.window (doubleHalfPublic K.M K.S)) s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size Spec.P256.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < Spec.P256.p) ∧
      (k < Spec.P256.curve.n → Rep Spec.P256.curve (tmv Spec.P256.curve K.M.n base s' K.R.x)
        (tmv Spec.P256.curve K.M.n base s' K.R.y) (tmv Spec.P256.curve K.M.n base s' K.R.z) (mul k P)) :=
  winJac_ok hL hp hC hM3 hO (doubleHalfPublic_dblOk hL.n4 hp hC hM3) hpn hone_lt hone n_mod32 n_ge64 hP hkJ
    hs hM hF

end VG.Proof.P256.X86_64
