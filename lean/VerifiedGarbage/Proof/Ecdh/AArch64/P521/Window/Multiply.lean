module

public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Core
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Mask
import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Layout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-! # The bounded working copy represents the original scalar whenever it is valid -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Window

attribute [local instance high] instPowNat

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64.P521Window
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem multiply_ok (hc : CfgOk c) (hC : Law c.C) (hO : PrimeOrder c.C) : MulOk c multiply := by
  intro base s hs g F P hP hpx hpy hrep rest R h
  rw [multiply]
  apply WP.assoc'
  refine WP.seq (WP.mono (mask_ok hs) fun s₁ ⟨hs₁,k₁,hm,U₁⟩ => ?_)
  have F₁ := F.unch hc.n10 hs.nowrap (fixedOk_slW (l := [K]) (by decide)) U₁
  have hv : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
    sv_unch U₁ hc.n10 hs.nowrap hi (apart_slW (by simpa using hne))
  have htv : ∀ {i}, i < 45 → i ≠ K →
      tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi hne; show toM _ _ (sv c base s₁ i) = toM _ _ (sv c base s i); rw [hv hi hne]
  refine core_ok c hc rfl (by decide +kernel) rfl (layout hc) (aligned hc) (inverse_spec hc) hC hO hs₁ F₁ hP
    (by rw [hv (by decide) (by decide)]; exact hpx)
    (by rw [hv (by decide) (by decide)]; exact hpy)
    (by rw [htv (by decide) (by decide),htv (by decide) (by decide),htv (by decide) (by decide)]; exact hrep)
    (by rw [hm]; exact Nat.mod_lt _ (by decide +kernel)) fun t ht => h t ?_
  refine ⟨ht.scr,ht.fixed,?_,?_,ht.rd.trans k₁.rd,ht.wr.trans k₁.wr,?_,?_,?_,
    ht.acc_lt,ht.acc,ht.rz_lt⟩
  · intro r hr
    have hnot : r ∉ [Reg.x3,.x4] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [ht.extra r hr,k₁.gpr r hnot]
  · rw [ht.x20,k₁.gpr .x20 (by decide)]
  · rw [ht.flag]
    apply U₁.word
    · intro w hw
      have hApart : ∀ w ∈ slW c [K], c.sl FLAG+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ c.sl FLAG :=
        apart_slW (by decide)
      have ha := hApart w hw
      rcases ha with ha | ha
      · left; have := hc.n0; omega
      · exact .inr ha
    · have := sl_le c hc.n10 (i := FLAG) (by decide); have := hs.nowrap; have := hc.n0; omega
  · rw [ht.d,hv (by decide) (by decide)]
  · intro hk1 hkn
    have hbits : c.C.n ≤ 2^521 := by decide +kernel
    have he : sv c base s₁ K = sv c base s K := by
      rw [hm,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hkn hbits)]
    have hq := ht.q
    rw [he] at hq
    exact hq hk1 hkn

end VG.Proof.Ecdh.AArch64.P521.Window
