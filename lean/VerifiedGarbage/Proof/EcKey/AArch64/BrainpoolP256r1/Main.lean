module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.GMul
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ### `Ecdsa.AArch64.BrainpoolP256r1.Main`, which only this module used -/

section

/-! # brainpoolP256r1 signing with the general ladder -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem stage₂ (hc : BaseCfgOk brainpoolp256r1) (hC : Law brainpoolp256r1.C)
    {s₀ : State} {base : Addr} {hs : Option Nat} {s : State} (hS : St₁ brainpoolp256r1 hs s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ brainpoolp256r1 hs s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq gMul (.seq brainpoolp256r1.pPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have F := hS.fixed
  have W := gMul_ok hc hC hS.scr F
  refine WP.seq (WP.mono W fun s₅ h₅ => ?_)
  obtain ⟨K₅, U₅, F₅, M₅, L₅, R₅⟩ := h₅
  rw [hS.k] at R₅
  have hs₅ := hS.scr.of_keepRegs K₅ (x0_not_powClob h7)
  refine WP.seq (WP.mono (pPow_ok hc hs₅ M₅
    (L₅ (brainpoolp256r1.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
    fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] →
      i ∉ [BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] →
      sv brainpoolp256r1 base s₆ i = sv brainpoolp256r1 base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_chainWc hc hi h₁)).trans (sv_unch U₅ h7 hn hi
      (apart_append (apart_slW (fun h => h₂ (by simp_all))) (apart_mulWF (.inl (by decide)) hi (fun h => h₂ (by simp_all)))))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv brainpoolp256r1 base s₆ i = sv brainpoolp256r1 base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_chainWc hc hi h₁)
  refine ⟨⟨hs₅.of_keepRegs K₆ (x0_not_powClob h7), ?_, by rw [K₆.wr, K₅.wr, hS.wr],
    F₅.unch h7 hn (fixedOk_chainWc hc) U₆⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flag_unch_chain hc U₆ h7 h0 hn, flag_unch_mulWF (.inl (by decide)) U₅ h7 h0 hn (by decide), hS.flag], ?_, lt₆, ?_,
    ?_⟩
  · rw [K₆.gpr _ (x20_not_powClob h7), K₅.gpr _ (x20_not_powClob h7), hS.x20]
  · show Rep brainpoolp256r1.C (toM _ _ (sv brainpoolp256r1 base s₆ RX)) (toM _ _ (sv brainpoolp256r1 base s₆ RY)) (toM _ _ (sv brainpoolp256r1 base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv brainpoolp256r1 base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (brainpoolp256r1.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1

end

end


/-! # brainpoolP256r1 public-key derivation without constant tables -/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, c.C.len⟩]
  wr : s.wr = [⟨s.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s.gpr .x2, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_d : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x1, c.C.len⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_fit : (s.gpr .x0).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64


theorem publicKeyWithStage_ok {c : Cfg} (hc : BaseCfgOk c) (hC : Law c.C)
    (mulCode : Prog isa)
    (hmul : ∀ {s₀ : State} {base : Addr} {s : State}, St₁ c none s₀ base s →
      WP isa (.seq mulCode (.seq c.pPow (.block []))) s (St₂ c none s₀ base))
    {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.AArch64.Cfg.publicKeyWith c mulCode) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono_syms (args_ok s₀) fun s₁ ⟨x4₁, x3₁, x2₁, k₁⟩ sy₁ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  have hp₁ : SetupPre c s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₁.wr, hp.wr, x4₁]; simp
    · rw [x3₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x1₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x2₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x1₁, x4₁]; exact hp.d_sc
    · rw [x2₁, x4₁]; exact hp.d_sc
    · rw [x3₁, x4₁]; exact hp.d_sc
    · rw [x4₁]; exact hp.sc_fit
  obtain ⟨t, s₂N, ex', S₂⟩ := stage₁ hc (.inl rfl) hp₁
    (rest := .seq mulCode (.seq c.pPow (.block [])))
    (Q := St₂ c none s₁ (s₁.gpr .x4)) fun _ S₁ =>
      hmul S₁
  rw [x4₁] at S₂
  let sN := s₁
  let s₂ := s₂N
  have g : ∀ r, sN.gpr r = s₁.gpr r := fun _ => rfl
  have mN : sN.mem = s₀.mem := k₁.mem
  have g₂ : s₂.gpr = s₂N.gpr := rfl
  have m₂ : s₂.mem = s₂N.mem := rfl
  have w₂ : s₂.wr = s₁.wr := S₂.wr
  have hwr₁ : s₁.wr = [⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s₀.gpr .x2, size⟩] := by rw [k₁.wr, hp.wr]
  have sv₂ : ∀ i, sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₂N i := fun _ => rfl
  have hs₂' : Scr s₂ (s₀.gpr .x2) size := S₂.scr
  have F₂ : Fixed c (s₀.gpr .x2) sN.gpr s₂.mem := S₂.fixed
  obtain ⟨t', s', exm, xv, yv, hxl, hx, hyl, hy, bytes, rax, saved⟩ :=
    middle_ok hc hs₂' F₂ (by rw [sv₂]; exact S₂.acc_lt) (by rw [m₂]; exact S₂.flag)
      (by rw [g₂, S₂.x20, g, x0₁]) hp.out_fit (by rw [w₂, hwr₁]; simp) hp.out_sc
  refine ⟨_, _, .seq ex' exm, fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4] := by decide
    rw [saved r hr, g, k₁.gpr r (hsv r hr)]
  -- The specification.
  have hk : kv c sN = dk c s₀ := by simp only [kv, dk, mN, g, x3₁]
  have hD : sv c (s₀.gpr .x2) s₂ D = dk c s₀ := by
    rw [sv₂, S₂.d, shAt_none, Nat.shiftRight_zero]; simp only [dv, dk, k₁.mem, x1₁]
  have hR := S₂.rep
  rw [hk] at hR
  have hZ : ∀ {i}, tmv c.C c.n (s₀.gpr .x2) s₂N (c.sl i) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ i) :=
    fun {i} => by rw [sv₂]
  have acc := S₂.acc
  rw [← sv₂, hZ] at acc
  rw [hZ, hZ, hZ] at hR
  have hxX : Fin.ofNat c.C.p xv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RX) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hx, acc]
  have hyY : Fin.ofNat c.C.p yv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RY) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hy, acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .x2) s₂ RZ) (by rw [sv₂]; exact S₂.rz_lt)
  unfold PkPost
  rw [publicKey_eq hC hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .x2) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega_using [h0])
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .x2) s₂ = true := decide_eq_true (by rw [hD]; omega_using [hd, h0])
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      rfl
  · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega_using [hd])
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

theorem publicKey_ok (hc : BaseCfgOk brainpoolp256r1) (hC : Law brainpoolp256r1.C)
    {s₀ : State} (hp : PkPre brainpoolp256r1 s₀) :
    WP isa Impl.EcKey.AArch64.publicKeyBrainpoolP256r1 s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost brainpoolp256r1 s₀ s' :=
  publicKeyWithStage_ok hc hC gMul
    (fun S => Ecdsa.AArch64.BrainpoolP256r1.stage₂ hc hC S fun _ S₂ => WP.block_nil S₂) hp

end VG.Proof.EcKey.AArch64.BrainpoolP256r1
