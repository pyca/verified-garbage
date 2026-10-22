module
public import VerifiedGarbage.Proof.Rsa.Arm.RvHalf

import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvCtx
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_recover_primes` on ARMv7: the numbers 0 and 1, and Montgomery multiplication's base

From the end of the halvings: the context with `w` words, `[aZ] := n - n =
0`, `[aOne] := 1`, and frame word 0 := `M0` with `r7 = w6` and `r3 = 0`,
as `setup` takes them (`montA_vp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- The arrays once 0 and 1 are set. -/
def A01 (P : RP) (σ : State) : Nat → Nat := upd (upd (Aload P σ) aZ 0) aOne 1

/-- The arrays 0, 1 and `n` live. -/
abbrev live01 : List Nat := [aOne, aZ, aN]

/-- The stage of the numbers 0, 1 and `n`, of `r` and of `t`. -/
abbrev K01 (P : RP) (σ : State) (s : State) : Prop :=
  KS P σ (A01 P σ) live01 (AWh P σ P.c) [wR, wM] (Vh P σ P.c) [sTc] s

section
variable {P : RP}

theorem rM_sub (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) : Region.Sub P.rM P.rS := by
  show Region.Sub ⟨State.addr P.M0, 8 * P.lenM⟩ ⟨State.addr P.B, P.Z⟩
  rw [M0_addr sz hf]
  refine Offset.sub_base _ ?_
  rw [sz.endM]; exact Nat.le_trans (arr_mono (show mBase + 8 ≤ nArr by decide)) sz.fits

theorem M0_toNat (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) : P.M0.toNat = P.B.toNat + P.oM := by
  have := sz.endM
  have := Nat.le_trans (arr_mono (w := P.w) (show mBase + 8 ≤ nArr by decide)) sz.fits
  have : 0 < P.lenM := by simp only [RP.lenM]; omega
  simp only [RP.M0, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := P.oM) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Zero, from `n - n`. -/
theorem zero_of_sub {X n w b : Nat} (hX : X < 2 ^ (32 * w)) (h : X + n = n + 2 ^ (32 * w) * b) (hb : b ≤ 1) :
    X = 0 := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega

theorem montA_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ HI P σ P.c s) montA
      (fun σ s => E σ ∧ K01 P σ s ∧ s.gpr .r0 = P.M0 ∧ s.gpr .r7 = BitVec.ofNat 32 P.w6 ∧ s.gpr .r3 = 0 ∧
        s.mem.readW (State.addr P.sp) 32 = P.M0) := by
  simp only [montA, seqs]
  let K1 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWh P σ P.c) [wR, wM] (Vh P σ P.c) [sTc, sCnt] s ∧
    Ws s P.B P.Z P.w nArr
  let K2 := fun σ s => E σ ∧ KS P σ (upd (Aload P σ) aZ 0) [aZ, aN] (AWh P σ P.c) [wR, wM] (Vh P σ P.c) [sTc, sCnt] s ∧
    Ws s P.B P.Z P.w nArr
  let K3 := fun σ s => E σ ∧ KS P σ (upd (upd (Aload P σ) aZ 0) aOne 0) [aOne, aZ, aN] (AWh P σ P.c) [wR, wM]
    (Vh P σ P.c) [sTc, sCnt] s ∧ Ws s P.B P.Z P.w nArr
  let K4 := fun σ s => E σ ∧ K01 P σ s ∧ Ws s P.B P.Z P.w nArr ∧ s.gpr .r0 = P.M0
  refine VP.seq (G := K1) ?_ (VP.seq (G := K2) ?_ (VP.seq (G := K3) ?_ ?_))
  -- The context.
  · refine VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨e, h, _⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r8, h₂.2.1.r8]
    · exact WP.mono (ctxw_ok h.bs h.r8 h.cnt) fun t ⟨ht, r, m⟩ => ⟨e, h.of_rest r m (by decide), ht⟩
  -- `[aZ] := n - n`.
  · refine VP.ctx zeroZ_taint (fun σ s h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
    refine WP.mono (h.sub3_w hw (o := aZ) (a := aN) (b := aN) (by decide) (by simp) (by simp) (by decide)
      (by decide) (by decide)) fun t ⟨X, ht, hwt, _, hx, hb⟩ => ⟨e, ?_, hwt⟩
    have hX : X < 2 ^ (32 * P.w) := by
      rw [← show num t.mem P.B P.w aZ = X by rw [ht.arrs aZ (by simp), upd_self]]
      exact val32_lt _ _ _ _
    rw [zero_of_sub hX hx hb] at ht
    exact ht
  -- `[aOne] := 0`.
  · refine VP.ctx oneZ_taint (fun σ s h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
    refine WP.mono (h.copy_w hw (o := aOne) (a := aZ) (by decide) (by simp) (by decide)
      (by decide)) fun t ⟨ht, hwt, _⟩ => ⟨e, ?_, hwt⟩
    rwa [upd_self] at ht
  -- `[aOne] := 1`, and `r0 := M0`.
  · rw [montSet_eq]
    refine VP.block_append (G := K4) (VP.ctx montHead_taint (fun σ s h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_) ?_
    · have sz := h.sizes
      have hf := h.bs.pre.fS
      refine h.setOne_w hw (j := aOne) (by simp) (by decide)
        fun s1 h1 hw1 _ => ?_
      refine ptr_ok hw1 (r := .r0) (by decide) (j := mBase) (by decide) fun s2 p2 r2 m2 hw2 => ?_
      refine wp_dp (op2_imm (by decide)) fun t u => WP.block_nil ⟨e, ?_, ?_, ?_⟩
      · have r := (r2.trans (u.rest (ws := [.r0]) (by simp)))
        have h2 := (h1.of_rest r (u.mem.trans m2) (by decide)).mono (A' := A01 P σ) (live' := live01)
          (AW' := AWh P σ P.c) (liveW' := [wR, wM]) (V' := Vh P σ P.c) (ls' := [sTc])
          (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩)
        · exact h2
        · simp only [live01, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl <;> simp [A01, upd, aOne, aZ, aN]
      · exact hw2.of_upd u (by decide) (by decide) (by decide)
      · rw [u.gpr, dpVal, p2, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl,
          add_ofNat_sub32 _ (by have : S P.w = 4 * (P.w + 2) := rfl; simp only [arr, hdr, mBase]; omega)]
    -- The stack.
    · refine VP.stack (by decide) (by decide) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw, r0⟩ => ?_
      · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
      have pre := h.bs.pre
      have sz := pre.sizes
      have spf := pre.spFit
      have sp : s.sp = P.sp := h.bs.sp.trans pre.sp
      refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
      have hc : (⟨State.addr P.sp, 4⟩ : Region).Contains (State.addr P.sp) (32 / 8) := by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
      refine wp_str (a := State.addr P.sp) (by decide)
        (by rw [h1.gpr, sp, BitVec.add_zero, BitVec.add_zero]) ⟨⟨State.addr P.sp, 56⟩,
          by rw [h1.wr, h.bs.wr, pre.wr]; simp, by
            simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩ fun u2 m2 => ?_
      have f0 : Frame [P.r0F] s.mem u2.mem := by
        rw [m2.mem, h1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
      have bs2 : Bs P σ u2 := ⟨pre, by rw [m2.sp, h1.sp]; exact h.bs.sp, by rw [m2.rd, h1.rd]; exact h.bs.rd,
        by rw [m2.wr, h1.wr]; exact h.bs.wr, by
          rw [m2.mem, h1.mem]; exact h.bs.frame.writeW (r := P.r0F) (by simp) _ hc⟩
      have k2 : K01 P σ u2 := h.of_outZ (outZ_of_frame0 h.bs f0) bs2 (by rw [m2.gpr, h1.other _ (by decide), h.r8])
      have sv : u2.mem.readW (State.addr P.sp) 32 = P.M0 := by
        rw [m2.mem, Mem.readW_writeW_self32, h1.other _ (by decide), r0]
      refine bs2.ldrSp (o := aoK) (by decide) (by decide) (by decide) fun u3 h3 => ?_
      refine wp_dp (op2_imm (by decide)) fun u4 h4 => ?_
      refine wp_mov (op2_lsr (by decide)) fun u5 h5 => ?_
      refine wp_mov (op2_imm (by decide)) fun t h6 => WP.block_nil ⟨e, ?_, ?_, ?_, ?_, ?_⟩
      · have r : Rest [.r7, .r3] u2 t := (h3.rest (by simp)).trans ((h4.rest (by simp)).trans
          ((h5.rest (by simp)).trans (h6.rest (by simp))))
        exact k2.of_rest r (by rw [h6.mem, h5.mem, h4.mem, h3.mem]) (by decide)
      · rw [h6.other _ (by decide), h5.other _ (by decide), h4.other _ (by decide), h3.other _ (by decide), m2.gpr,
          h1.other _ (by decide), r0]
      · rw [h6.other _ (by decide), h5.gpr, h4.gpr, dpVal, h3.gpr, pre.aK]
        have k2 := pre.k2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
          BitVec.toNat_ofNat, show (7 : BitVec 32).toNat = 7 from rfl]
        simp only [RP.w6]
        omega
      · rw [h6.gpr]
      · rw [h6.mem, h5.mem, h4.mem, h3.mem]; exact sv

end

end VG.Proof.Rsa.Arm.Recover
