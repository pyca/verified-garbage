import VerifiedGarbage.Proof.AesSiv.Arm.Open
import VerifiedGarbage.Proof.AesGcm.Arm.CTBase

/-!
# AES-SIV on ARMv7: the CMAC of a string is constant time

Untrusted: everything here is checked by Lean. Two runs of `cmacOf` on
strings at the same address and of the same length (`MPre`) leak the same:
the blocks between the calls the taint analysis checks from the registers
that hold the string's address and length, the context, the rounds and `W`;
the calls get the same arguments in both runs (`upd_rel`, `fin_rel`), which
the correctness lemmas give.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- The registers an environment fixes. -/
theorem env_eq {c w sp : BitVec 32} {R : Nat} {s₁ s₂ : State} (h₁ : Env c w sp R s₁) (h₂ : Env c w sp R s₂)
    {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `cmacOf`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
structure MPre (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  buf : Buf w sp s P n
  r6 : s.gpr .r6 = P
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- What the bytes after the chained ones are, as a buffer. -/
theorem Buf.rest {w sp P : BitVec 32} {n : Nat} {s : State} (hP : Buf w sp s P n) :
    Buf w sp s (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
  have hcl := chainedLen_le n
  by_cases h0 : n - Spec.Cmac.chainedLen 16 n = 0
  · have : n = 0 := by
      by_contra hne; have := chainedLen_ne hne; omega
    subst this
    rw [chainedLen_zero, show P + BitVec.ofNat 32 0 = P from BitVec.add_zero P]
    exact hP
  · exact hP.sub (j := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega) (by omega)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Between the calls of `cmacOf`. -/
structure MMid (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)

theorem cmacOf_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (MPre c w sp R P n) (cmacOf stOff) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      (cmacPre stOff) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r9, .r10, .r11])
      (.block (cmacMid stOff)) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => MMid c w sp R P n s ∧
      UArgs s c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r5, h₂.r5]
      · rw [h₁.r6, h₂.r6]
      all_goals exact env_eq h₁.env h₂.env (by simp)) hA)
    (fun s h => WP.mono (cmacPre_ok L h.env hR h.buf hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, U, _⟩ =>
      ⟨⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r6], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r5]⟩, h4⟩, U⟩) ?_
  refine CT.seq (J := MMid c w sp R P n)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.pre.env.sp, hh.2.1.pre.env.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => by
      have g : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := h'.saved
      exact ⟨⟨h.1.pre.env.of_saved h'.saved h'.sp h'.rd h'.wr, h.1.pre.buf.of_eq h'.rd h'.wr,
        by rw [g _ (by decide) (by decide), h.1.pre.r6], by rw [g _ (by decide) (by decide), h.1.pre.r5]⟩,
        by rw [g _ (by decide) (by decide), h.1.r4]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ FArgs s c (w + BitVec.ofNat 32 stOff)
      (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (w + BitVec.ofNat 32 256) (n - Spec.Cmac.chainedLen 16 n) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r5, h₂.pre.r5]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact env_eq h₁.pre.env h₂.pre.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := cmacMid_ok L h.pre.env hR hn h.pre.buf.rest h.r4 h.pre.r5 h.pre.r6
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-! ## S2V over the components -/

/-- The descriptors' words in `m` are `dsc`, the same in both runs. -/
def DescEq (m : Mem) (a : BitVec 32) (N : Nat) (dsc : Nat → Nat → BitVec 32) : Prop :=
  ∀ i < N, ∀ j < 2, descW m a i j = dsc i j

/-- Before component `i` (and, for `i = N`, after the last), in one run. -/
def AI (c w sp a : BitVec 32) (R N : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ m₀ σ, AInv c w sp a R N m₀ σ i s ∧ DescEq m₀ a N dsc

/-- One component. -/
theorem adBody_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) :
    CT (AI c w sp a R N dsc i) (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r8]) (.block adNext) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
      (.block adStep) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => MPre c w sp R (dsc i 0) (dsc i 1).toNat s ∧
      s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧ s.gpr .r7 = BitVec.ofNat 32 (N - i))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r8, h₂.r8]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => WP.mono (adNext_ok h.ads hi h.frame h.r8) fun s₁ ⟨h6, h5, g, k⟩ => by
      have hb := (h.ads.comp i hi).of_eq k.rd k.wr
      rw [hd i hi 0 (by decide), hd i hi 1 (by decide)] at hb
      exact ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr, hb,
        by rw [h6, hd i hi 0 (by decide)],
        by rw [h5, hd i hi 1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
        by rw [g _ (by decide) (by decide), h.r8], by rw [g _ (by decide) (by decide), h.r7]⟩) ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧ s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧
      s.gpr .r7 = BitVec.ofNat 32 (N - i))
    ((cmacOf_ct L hR (BitVec.isLt _)).mono fun s h => h.1)
    (fun s h => WP.mono (cmacOf_ok L h.1.env hR h.1.buf (BitVec.isLt _) h.1.r6 h.1.r5)
      fun s' ⟨he, _, _, g, _, _⟩ => ⟨he, by rw [g _ (by decide) (by decide) (by decide), h.2.1],
        by rw [g _ (by decide) (by decide) (by decide), h.2.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]
    all_goals exact env_eq h₁.1 h₂.1 (by simp)) hC

/-- One component, as `aStep_ok` but with the descriptors. -/
theorem adBody_wp {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) {s : State}
    (h : AI c w sp a R N dsc i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) s fun s' =>
      AI c w sp a R N dsc (i + 1) s' ∧ s'.z = decide (N - (i + 1) = 0) := by
  obtain ⟨m₀, σ, h, hd⟩ := h
  exact WP.mono (aStep_ok L hR h hi) fun s' ⟨h', hz⟩ => ⟨⟨m₀, σ, h', hd⟩, hz⟩

/-- S2V over the components. -/
theorem s2vAds_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (AI c w sp a R N dsc 0) s2vAds := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7]) (.block [.cmp .r7 (imm 0)])
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => AI c w sp a R N dsc 0 s ∧ s.z = decide (N = 0))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => by
      refine WP.of_runBlock ⟨_, by arun [], ⟨m₀, σ, ?_, hd⟩, ?_⟩
      · exact ⟨h.env.keep (fun r _ => rfl) rfl rfl rfl, h.ads.of_eq rfl rfl, h.r8, h.r7, h.rd, h.wr, h.frame,
          h.acc⟩
      · simp only [Proof.AesGcm.Arm.z_subFlags, h.r7, Nat.sub_zero]; exact Proof.AesGcm.Arm.z_cmp hN (by decide))
    ?_
  refine CT.ite (decide (N = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hN0 => ?_
  have hN0' : N ≠ 0 := by simpa using hN0
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (k : Nat) (x y : State) => ∃ i, k = N - i ∧ i < N ∧ AI c w sp a R N dsc i x ∧ AI c w sp a R N dsc i y)
    (fun k => ?_) (N - 0)).mono (fun x y hxy => ⟨0, rfl, Nat.pos_of_ne_zero hN0', hxy.1.1, hxy.2.1⟩)
    fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : k = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (((adBody_ct L hR hiN).wp
    (F₁ := fun (s : State) => AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    (F₂ := fun (s : State) => AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    fun x y hxy => ⟨adBody_wp L hR hiN hxy.1, adBody_wp L hR hiN hxy.2⟩).mono
    (fun x y p => ⟨p.2.2.1, p.2.2.2⟩) fun x y p => ?_)
  have ea := Proof.AesGcm.Arm.eval_ne' p.2.1.2
  have eb := Proof.AesGcm.Arm.eval_ne' p.2.2.2
  refine ⟨by rw [ea, eb], fun e => trivial, fun e => ?_⟩
  have he : N - (i + 1) ≠ 0 := by rw [ea] at e; simpa using e
  exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, p.2.1.1, p.2.2.1⟩

end

end VG.Proof.AesSiv.Arm
