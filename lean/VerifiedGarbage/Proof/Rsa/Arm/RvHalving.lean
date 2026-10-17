module

public import VerifiedGarbage.Proof.Rsa.Arm.RvHalf
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: `m = 2^t r` (`halving_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (halveStep)

section
variable {P : RP}

theorem ws_regs {s₁ s₂ : State} {v N : Nat} (h₁ : Ws s₁ P.B P.Z v N) (h₂ : Ws s₂ P.B P.Z v N) :
    ∀ r ∈ [Reg.r7, .r8, .r9], s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

theorem halfInit_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWs P σ) [wM, wZ] (Vs P σ) [sBit] s ∧ Ws s P.B P.Z P.W 22)
      halfInit (fun σ s => E σ ∧ HI P σ 0 s) := by
  have eI : halfInit = .seq (copy wR wM) (.block ([.mov .r1 (.imm 0), .str .r1 .r8 sTc] ++
      ([.ldrSp .r1 aoEl, .ldrSp .r2 aoDl] ++ [.dp .add .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsl 3),
        .str .r1 .r8 sCnt]))) := rfl
  rw [eI]
  let K1 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (upd (AWs P σ) wR (mv P σ)) [wR, wM, wZ] (Vs P σ) [sBit] s ∧
    Ws s P.B P.Z P.W 22
  let K2 := fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (upd (AWs P σ) wR (mv P σ)) [wR, wM, wZ]
    (upd (Vs P σ) sTc 0) [sTc, sBit] s ∧ Ws s P.B P.Z P.W 22
  let K3 := fun σ s => K2 σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.el ∧ s.gpr .r2 = BitVec.ofNat 32 P.dl
  refine VP.seq (G := K1) ?_ (VP.block_append (G := K2) ?_ (VP.block_append (G := K3) ?_ ?_))
  · refine VP.taint _ copyRM_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ws_regs h₁.2.2 h₂.2.2) fun σ s ⟨e, h, hw⟩ => ?_
    refine WP.mono (h.copy_W hw (o := wR) (a := wM) (by decide) (by simp) (by decide)
      (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun t ⟨ht, hwt, _⟩ => ⟨e, ?_, hwt⟩
    have : AWs P σ wM = mv P σ := by simp [AWs, upd_self]
    rw [this] at ht; exact ht
  · refine VP.taint [.r8] tZero_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.r8, h₂.2.2.r8]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r1]) (by simp)) u1.mem
    refine h1.strSlot hw1 (d := sTc) (r := .r1) (by decide) fun t ht hwt _ _ => WP.block_nil ⟨e, ?_, hwt⟩
    rw [u1.gpr] at ht; exact ht
  · show VP _ (.block ([(Reg.r1, aoEl), (Reg.r2, aoDl)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · refine h.bs.ldrSp (o := aoEl) (by decide) (by decide) (by decide) fun s1 u1 => ?_
      obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r1]) (by simp)) u1.mem
      refine h1.bs.ldrSp (o := aoDl) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
      obtain ⟨ht, hwt⟩ := h1.reg hw1 (u2.rest (ws := [.r2]) (by simp)) u2.mem
      exact ⟨⟨e, ht, hwt⟩, by rw [u2.other _ (by decide), u1.gpr, h.bs.pre.aEl], by rw [u2.gpr, h.bs.pre.aDl]⟩
  · refine VP.taint [.r8] cntStore_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hw⟩, r1, r2⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    have el2 := h.bs.pre.el2; have dl2 := h.bs.pre.dl2; have k2 := h.bs.pre.k2
    refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
    obtain ⟨h2, hw2⟩ := h.reg hw ((u1.rest (ws := [.r1]) (by simp)).trans (u2.rest (by simp)))
      (u2.mem.trans u1.mem)
    refine h2.strSlot hw2 (d := sCnt) (r := .r1) (by decide) fun t ht hwt _ _ => WP.block_nil ⟨e, ?_, hwt⟩
    have c : (s2.gpr .r1).toNat = P.c := by
      rw [u2.gpr, u1.gpr, dpVal, r1, r2]
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [RP.c]
      omega
    rw [c] at ht
    refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_)
    · simp only [List.mem_singleton] at hj; subst hj
      exact ⟨by simp, by simp [AWh, hvs, upd_self]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simp, by rw [upd_ne _ _ (by decide), upd_self]; simp [Vh, hvs, upd, sTc, sCnt]⟩
      · exact ⟨by simp, by rw [upd_self]; simp [Vh, upd]⟩

theorem halving_vp {E : State → Prop} (hE : ∀ σ, E σ → 0 < P.c) :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [aN] (AWs P σ) [wM, wZ] (Vs P σ) [sBit] s ∧ Ws s P.B P.Z P.W 22)
      halving (fun σ s => E σ ∧ HI P σ P.c s) := by
  refine halfInit_vp.seq ?_
  -- The loop, with `n + 1` halvings left.
  let I := fun n σ s => E σ ∧ n ≤ P.c ∧ HI P σ (P.c - n) s
  have hl := VP.loop (I := I) (body := halfBody) (c := .ne) (Q := fun σ s => E σ ∧ HI P σ P.c s) (fun n => ?_)
  · refine VP.mono (F := fun σ s => E σ ∧ HI P σ 0 s) (?_ : VP _ _ _) (fun _ _ h => h) (fun _ _ h => h)
    refine ⟨fun σ s ⟨e, h⟩ => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ e₁' e₂' => ?_⟩
    · have hc := hE σ e
      refine (hl (P.c - 1)).wp σ s ⟨e, by omega, ?_⟩
      rw [show P.c - (P.c - 1 + 1) = 0 by omega]; exact h
    · have hc := hE σ₁ e₁
      exact (hl (P.c - 1)).ct s₁ s₂ t₁ t₂ s₁' s₂'
        ⟨σ₁, σ₂, ⟨e₁, by omega, by rw [show P.c - (P.c - 1 + 1) = 0 by omega]; exact h₁⟩,
          ⟨e₂, by omega, by rw [show P.c - (P.c - 1 + 1) = 0 by omega]; exact h₂⟩⟩ e₁' e₂'
  · refine VP.taint _ halfBody_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ws_regs h₁.2.2.2 h₂.2.2.2)
      fun σ s ⟨e, hn, h⟩ => ?_
    refine WP.mono (halfBody_ok h (by omega)) fun t ⟨ht, zt⟩ => ⟨?_, fun h0 => ?_, fun hp => ?_⟩
    · show some (!t.z) = some (decide (0 < n))
      rw [zt, show P.c - (P.c - (n + 1) + 1) = n by omega]
      by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero]
    · subst h0; refine ⟨e, ?_⟩; rw [show P.c - (0 + 1) + 1 = P.c by omega] at ht; exact ht
    · refine ⟨e, by omega, ?_⟩; rw [show P.c - (n + 1) + 1 = P.c - n by omega] at ht; exact ht

end

end VG.Proof.Rsa.Arm.Recover
