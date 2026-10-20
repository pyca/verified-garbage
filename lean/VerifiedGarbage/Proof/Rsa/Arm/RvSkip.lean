module

public import VerifiedGarbage.Proof.Rsa.Arm.RvProd2
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq

/-! # `vg_rsa_recover_primes` on ARMv7: the test of `M` (`skip_vp`), and the numbers (`numbers_vp`)

`M`'s low bit into `sBit`, `m = 2 (M / 2)` (`M - 1` for an odd `M`), and Z
set iff `M` is odd and `m` is not zero: iff candidates are tried.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `m`. -/
abbrev mv (P : RP) (σ : State) : Nat := 2 * (Mv P σ / 2)

/-- Whether candidates are tried. -/
abbrev goOn (P : RP) (σ : State) : Bool := decide (Mv P σ % 2 = 1 ∧ 0 < mv P σ)

/-- The arrays with `W` words after the test. -/
def AWs (P : RP) (σ : State) : Nat → Nat := upd (AWp P σ) wM (mv P σ)

/-- The header words after the test. -/
def Vs (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sBit (Mv P σ % 2)

section
variable {P : RP}

theorem skip_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWp P σ) [wM, wMod, wZ] (fun _ => 0) [] s ∧
        Ws s P.B P.Z P.W 22)
      (.seq (.block skipBits) (.seq (sub3 wT wZ wM) (.block skipTest)))
      (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWs P σ) [wM, wZ] (Vs P σ) [sBit] s ∧
        Ws s P.B P.Z P.W 22 ∧ s.z = goOn P σ) := by
  refine VP.taint [.r7, .r8, .r9] skip_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [h₁.2.2.r7, h₂.2.2.r7]
    · rw [h₁.2.2.r8, h₂.2.2.r8]
    · rw [h₁.2.2.r9, h₂.2.2.r9]
  have gM : AWp P σ wM = Mv P σ := by simp [AWp, upd]
  have gZ : AWp P σ wZ = 0 := by simp [AWp, AW1, upd, wM, wMod, wZ, wD, wE]
  refine WP.seq ?_
  unfold skipBits
  refine h.bitOf_W hw (j := wM) (by simp) (by decide) fun s1 h1 hw1 r1 => ?_
  rw [← List.append_nil (clrLow wM)]
  refine h1.clrLow_W hw1 (j := wM) (by simp) (by simp only [List.mem_singleton]; rintro i rfl; decide)
    fun s2 h2 hw2 r2 => WP.block_nil ?_
  refine WP.seq (WP.mono (h2.sub3_W hw2 (o := wT) (a := wZ) (b := wM) (by decide) (by simp) (by simp) (by decide)
    (by decide) (by simp only [List.mem_singleton]; rintro i rfl; decide)) fun s3 ⟨X, h3, hw3, r3, v3, b3⟩ => ?_)
  rw [upd_self, upd_ne _ _ (by decide), gZ, gM] at v3
  have hX : X < 2 ^ (32 * P.W) := by
    have := h3.arrsW wT (by simp); rw [upd_self] at this; rw [← this]; exact val32_lt _ _ _ _
  have emv : mv P σ = 2 * (Mv P σ / 2) := rfl
  have hb : (s3.gpr .r11).toNat = if 0 < mv P σ then 1 else 0 := by
    have := borrow_iff (P := 2 ^ (32 * P.W)) v3 hX b3
    split <;> omega
  unfold skipTest
  refine wp_ldrSlot hw3 (d := sBit) (by decide) fun s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t u6 z6 => WP.block_nil ?_
  have rt : Rest [.r1] s3 t := (u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest _))
  have mt : t.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  refine ⟨e, (h3.of_rest rt mt (by decide)).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_),
    hw3.rest rt, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨by simp, by rw [upd_ne _ _ (by decide), upd_self, gM]; simp only [AWs, upd_self]⟩
    · exact ⟨by simp, by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), gZ, AWs, upd_ne _ _ (by decide), gZ]⟩
  · simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by simp, by simp only [Vs, upd_self, gM]⟩
  · have hs : slot s3.mem P.B sBit = Mv P σ % 2 := by
      rw [h3.sl sBit (by simp), upd_self, gM]
    have e4 : s4.gpr .r1 = BitVec.ofNat 32 (Mv P σ % 2) := by
      rw [u4.gpr]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : Mv P σ % 2 < 2 ^ 32)]; exact hs
    rw [z6, u5.gpr, dpVal, e4, u4.other _ (by decide)]
    have h11 : s3.gpr .r11 = BitVec.ofNat 32 (if 0 < mv P σ then 1 else 0) := by
      apply BitVec.eq_of_toNat_eq; rw [hb, BitVec.toNat_ofNat]; split <;> rfl
    rw [h11]
    simp only [goOn]
    rcases Nat.mod_two_eq_zero_or_one (Mv P σ) with c | c <;> by_cases hm : 0 < mv P σ <;>
      simp only [c, hm, ite_true, ite_false] <;> decide

end

end VG.Proof.Rsa.Arm.Recover
