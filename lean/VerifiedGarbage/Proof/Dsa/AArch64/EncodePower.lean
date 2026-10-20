module

public import VerifiedGarbage.Proof.Dsa.AArch64.Product
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest

/-! # Preparing ordinary operands for DSA exponentiation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Encode an arbitrary base fitting the workspace width and initialize
the exponentiation accumulator to the Montgomery representation of one. -/
theorem encodePower_ok (M : Mont) {s : State} {B : Addr} {Z w m x : Nat} {minv : BitVec 64}
    (hc : ModCtx s B Z w minv m) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hx : wv s.mem B (slot w aX) w = x)
    (hR2 : wv s.mem B (slot w aR2) w = (2 ^ (64 * w) * 2 ^ (64 * w)) % m)
    (hone : wv s.mem B (slot w aOne) w = 1) :
    WP isa (Arithmetic.encodePower M.mm) s fun t =>
      ModCtx t B Z w minv m ∧
      wv t.mem B (slot w Crt.aXc) w = x * 2 ^ (64 * w) % m ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % m ∧
      wv t.mem B (slot w aOne) w = 1 ∧
      Arrays B w [aAcc, aTmp, aR2, aXm, aY] s.mem t.mem ∧ Keep mmRegs s t := by
  have hm0 : 0 < m := by omega
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  have hR := coprime_pow2 hodd (64 * w)
  unfold Arithmetic.encodePower
  refine WP.seq (WP.mono (mont_step M hc hZ hw hw' (by unfold MmUse; decide)
    (by rw [hone]; exact hm)) fun u ⟨hcu, hlu, hvu, hfu, hku⟩ => ?_)
  rw [hone] at hvu
  have hR2mod : wv s.mem B (slot w aR2) w % m = 2 ^ (64 * w) * 2 ^ (64 * w) % m := by
    rw [hR2, Nat.mod_mod]
  have uy := VG.Proof.Dsa.mont_decode hR hR2mod hvu
  rw [Nat.mod_eq_of_lt hlu] at uy
  have ux : wv u.mem B (slot w aX) w = x :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hx
  have ur2 : wv u.mem B (slot w aR2) w = (2 ^ (64 * w) * 2 ^ (64 * w)) % m :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hR2
  have uone : wv u.mem B (slot w aOne) w = 1 :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hone
  refine WP.seq (WP.mono (mont_step M hcu hZ hw hw' (by unfold MmUse; decide)
    (by rw [ur2]; exact Nat.mod_lt _ hm0)) fun v ⟨hcv, hlv, hvv, hfv, hkv⟩ => ?_)
  rw [ux, ur2] at hvv
  have vx := VG.Proof.Dsa.mont_scale hR hvv
  rw [Nat.mod_eq_of_lt hlv] at vx
  have vy : wv v.mem B (slot w aY) w = 2 ^ (64 * w) % m :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans uy
  have vone : wv v.mem B (slot w aOne) w = 1 :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans uone
  refine WP.mono (copyArr_ok hcv.good hZ (by omega) hw' (by decide) (by decide) (by decide))
    fun t ⟨hcopy, hf, hk⟩ => ?_
  have hfa : Arrays B w [aR2] v.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) hf (Nat.le_refl _)
      (by change slot w 4 + 8 * w ≤ slot w 4 + 8 * (w + 2); omega)
  have htg : Good t B Z w minv :=
    ⟨hcv.good.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hcv.good.x0, hfa.hdr hcv.good.hdr⟩
  have htn : wv t.mem B (slot w aN) w = m :=
    (hfa.wv_of_not_mem (by decide) (by decide) hnZ).trans hcv.modulus
  have hti : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hnZ (by omega)]
    exact hcv.inverse
  refine ⟨⟨htg, htn, hti⟩, hcopy.trans vx,
    (hfa.wv_of_not_mem (by decide) (by decide) hnZ).trans vy,
    (hfa.wv_of_not_mem (by decide) (by decide) hnZ).trans vone,
    ?_, ((hku.trans hkv).trans hk).mono (by decide)⟩
  have f1 : Arrays B w [aAcc, aTmp, aR2, aXm, aY] s.mem u.mem := hfu.mono (by decide)
  have f2 : Arrays B w [aAcc, aTmp, aR2, aXm, aY] u.mem v.mem := hfv.mono (by decide)
  have f3 : Arrays B w [aAcc, aTmp, aR2, aXm, aY] v.mem t.mem := hfa.mono (by decide)
  exact (f1.trans f2).trans f3

end VG.Proof.Dsa.AArch64
