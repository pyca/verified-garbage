import VerifiedGarbage.Proof.EcKey.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified

/-! # P-256 public-key generation with a fixed-base comb -/
namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (YM Y Args.publicKey)

variable {c : Cfg}

theorem publicKeyCombBody_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C)
    {s₀ : State} {extra : List Region} (hp : PkPre c s₀ extra)
    (hTb : ∀ d, c.comb = some d → TblMem s₀ ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs (ptr s₀ 2) ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa (.seq (c.prepareWith Args.publicKey) (.seq c.gMul (.seq c.pPow
      (Impl.EcKey.X86.Cfg.middle c)))) s₀ fun s' => PkKeep c s₀ s' ∧ PkPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (stage₁ hc hp.setup (rest := .block [])
    (Q := St₁ c Args.publicKey s₀ (ptr s₀ 2)) (fun _ h => WP.block_nil h)) fun s₁ S₁ => ?_)
  refine stage₂Comb hc hC hT hCo ham3 S₁ hTb fun s₂ S₂ => ?_
  have h3 : (s₀.gpr .esp).toNat + 4 + 4 * 3 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  refine WP.mono (middle_ok hc S₂.scr S₂.fixed S₂.acc_lt S₂.flag S₂.whole S₂.esp S₂.rd S₂.wr
    ⟨_, by rw [hp.rd]; simp, arg_containsN h3 (by decide)⟩ (hp.args_sc.sub_left (arg_subN h3 (by decide)))
    hp.out_fit (by rw [hp.wr]; simp) hp.out_sc)
    fun s' ⟨xv, yv, hxl, hx, hyl, hy, bytes, rax, saved, esp, frame⟩ => ⟨⟨saved, esp, frame⟩, ?_⟩
  -- The specification.
  have hD : sv c (ptr s₀ 2) s₂ D = dk c s₀ := by rw [S₂.d, dv_eq (A := Args.publicKey) rfl]
  have hR := S₂.rep
  have hxX : Fin.ofNat c.C.p xv = tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RX) *
      tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hx, S₂.acc]
  have hyY : Fin.ofNat c.C.p yv = tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RY) *
      tmv c.C c.n (ptr s₀ 2) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hy, S₂.acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (ptr s₀ 2) s₂ RZ) S₂.rz_lt
  unfold PkPost
  have hdk : dk c s₀ = kv c Args.publicKey s₀ := (kv_eq (A := Args.publicKey) rfl).symm
  rw [hdk, publicKey_eq hC hR hxl hxX hyl hyY, ← hdk]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (ptr s₀ 2) s₂ RZ = 0
    · have hok : ok c (ptr s₀ 2) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (ptr s₀ 2) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      show _ = 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
      rfl
  · have hok : ok c (ptr s₀ 2) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.EcKey.X86
