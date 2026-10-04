import VerifiedGarbage.Proof.AesSiv.Arm.CTMac

/-!
# AES-SIV on ARMv7: S2V's end is constant time

Untrusted: everything here is checked by Lean. Two runs of `finish` on
strings at the same address and of the same length (`FI`) leak the same:
the branch is on the length, and so are the tails' copies and `j`, which
the taint analysis checks with the blocks between the calls; the calls get
the same arguments in both runs, which the correctness lemmas give
(`shortArgs_ok`, `longArgs₁_ok`, `longArgs₂_ok`, `longArgs₃_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- Before `finish`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
abbrev FI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) : State → Prop := MPre c w sp R P n

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
theorem env_regs {s₁ s₂ : State} (h₁ : Env c w sp R s₁) (h₂ : Env c w sp R s₂) :
    ∀ r ∈ ([.r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact env_eq h₁ h₂ (by simp)

/-- The short case's call. -/
theorem shortMac_ct {out : Nat} (hout : out = 0 ∨ out = tOff) : CT (Env c w sp R) (shortMac out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (shortArgs out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact CT.seq (J := fun s => Env c w sp R s ∧
      FArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => env_regs h₁ h₂) hA)
    (fun s h => WP.mono (shortArgs_ok L h hR hout) fun s' h' => ⟨h'.1, h'.2.2.2.2.2⟩)
    (fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩)

/-- Before the long case's calls: the string and `16 k`. -/
structure LI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)

/-- The long case's calls. -/
theorem longMac_ct {P : BitVec 32} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : CT (LI c w sp R P n) (longMac out) := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r6, .r9, .r10, .r11])
      (.block (longArgs₁ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5]) jBlock h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r9, .r10, .r11])
      (.block (longArgs₂ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r7, .r9, .r10, .r11])
      (.block (longArgs₃ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The registers the pieces keep.
  let K := 16 * kOf n
  let j := jOf n
  let Rg (s : State) : Prop := Env c w sp R s ∧ s.gpr .r4 = BitVec.ofNat 32 K ∧ s.gpr .r5 = BitVec.ofNat 32 n
  have keep : ∀ {s s' : State}, Rg s → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      s'.rd = s.rd → s'.wr = s.wr → Rg s' := fun h g hsp hrd hwr =>
    ⟨h.1.of_saved g hsp hrd hwr, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩
  refine CT.seq (J := fun s => Rg s ∧ UArgs s c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact env_eq h₁.pre.env h₂.pre.env (by simp)) hA)
    (fun s h => WP.mono (longArgs₁_ok L h.pre.env hR h.pre.buf (K := K) (by omega) (by omega) hn h.pre.r6 h.r4 hout)
      fun s' ⟨he, g, _, _, _, U⟩ => ⟨⟨he, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h.r4], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h.pre.r5]⟩, U⟩) ?_
  refine CT.seq (J := Rg) (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.sp, hh.2.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => keep h.1 h'.saved h'.sp h'.rd h'.wr) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2]) hB)
    (fun s h => WP.mono (jBlock_ok h16 hn h.2.2) fun s' ⟨h7, g, k⟩ =>
      ⟨⟨h.1.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr,
        by rw [g _ (by decide) (by decide), h.2.1], by rw [g _ (by decide) (by decide), h.2.2]⟩, h7⟩) ?_
  refine CT.seq (J := fun s => (Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j) ∧
      UArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      all_goals exact env_eq h₁.1.1 h₂.1.1 (by simp)) hC)
    (fun s h => by
      obtain ⟨s', run, he, g, k, U⟩ := longArgs₂_ok L h.1.1 hR hout hj1 h.2
      refine WP.of_runBlock ⟨s', run, ⟨⟨he, ?_, ?_⟩, ?_⟩, U⟩
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.1]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.2]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2]) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.1.sp, hh.2.1.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => ⟨keep h.1.1 h'.saved h'.sp h'.rd h'.wr,
      by rw [h'.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ FArgs s c (w + BitVec.ofNat 32 out)
      (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256) (n - K - 16 * j) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2, h₂.1.2.2]
      · rw [h₁.2, h₂.2]
      all_goals exact env_eq h₁.1.1 h₂.1.1 (by simp)) hD)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := longArgs₃_ok L h.1.1 hR hout hn hT hJ hj1 h.2 h.1.2.2 h.1.2.1
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-- S2V's end with the string, into `W + out`. -/
theorem finish_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    CT (FI c w sp R P n) (finish out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hS⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      shortTail h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hL⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      longTail h).isSome = true := ⟨_, by taint_decide⟩
  have regs : ∀ s₁ s₂, FI c w sp R P n s₁ → FI c w sp R P n s₂ →
      ∀ r ∈ ([.r5, .r6, .r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6]
    all_goals exact env_eq h₁.env h₂.env (by simp)
  refine CT.seq (J := fun s => FI c w sp R P n s ∧ s.z = decide (n / 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, hz, g, k⟩ := finishPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.buf.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2) (fun ht => ?_) fun hf => ?_
  · have h16 : n < 16 := by have := of_decide_eq_true ht; omega
    exact (CT.seq (J := Env c w sp R) (CT.taint _ regs hS)
      (fun s h => WP.mono (shortTail_ok L h.env h.buf h16 h.r6 h.r5) fun s' h' => h'.1)
      (shortMac_ct L hR hout)).mono fun s h => h.1
  · have h16 : 16 ≤ n := by have := of_decide_eq_false hf; omega
    exact (CT.seq (J := LI c w sp R P n) (CT.taint _ regs hL)
      (fun s h => WP.mono (longTail_ok L h.env h.buf h16 hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, _⟩ =>
        ⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide), h.r6],
          by rw [g _ (by decide) (by decide) (by decide), h.r5]⟩, h4⟩)
      (longMac_ct L hR h16 hn hout)).mono fun s h => h.1

end

end VG.Proof.AesSiv.Arm
