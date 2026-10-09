import VerifiedGarbage.Proof.AesCcm.Arm.CTBase

/-!
# AES-CCM on ARMv7: the MAC is constant time

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` get the same arguments in both runs (`updBlock_ct`,
`Proof.AesCcm.Arm.upd_rel`); the branches are on the lengths, public; the
blocks between the calls the taint analysis checks.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (CT copyLoop_ok bytesAt_frame)
open VG.Proof.AesCcm (headLen)

/-- Before a piece chaining the `len` bytes at `P`. -/
def AbsI (k w sp : BitVec 32) (R q1 : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop :=
  Env k w sp R q1 s ∧ (len ≠ 0 → Buf w sp s P len) ∧ s.gpr .r4 = P ∧ s.gpr .r5 = BitVec.ofNat 32 len

theorem env_eq {k w sp : BitVec 32} {R q1 : Nat} {s₁ s₂ : State} (h₁ : Env k w sp R q1 s₁) (h₂ : Env k w sp R q1 s₂)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `updBlock y`. -/
theorem updBlock_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (Env k w sp R q1) (updBlock y) := by
  refine CT.seq (J := fun s => UArgs s k (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 384)
    R 1 ∧ s.sp = sp) ?_ (fun s he => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁ h₂ (by simpa using hr)) hc
  · obtain ⟨s₁, run₁, U, he₁, -, -⟩ := updBlockArgs_ok L he hR hy
    exact WP.of_runBlock ⟨s₁, run₁, U, he₁.sp⟩
  · exact upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The whole blocks of a string. -/
theorem absorbWhole_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbWhole y) := by
  refine CT.seq (J := fun s => AbsI k w sp R q1 P len s ∧ s.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧
    s.z = decide (len / 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := split16_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h12, hz⟩
  refine CT.ite (decide (len / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len / 16 ≠ 0 := by simpa using hb
  refine CT.seq (J := fun s => UArgs s k (w + BitVec.ofNat 32 y) P (w + BitVec.ofNat 32 384) R (len / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, hP, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [.mov .r3 (.reg .r4)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₂, run₂, U, he₂, -, -⟩ := absArgs_ok L he hR hy ((hP (by omega_arith)).take (Nat.mul_div_le len 16))
      (by omega_arith) h4 h12
    exact WP.of_runBlock ⟨s₂, run₂, U, he₂.sp⟩
  · exact upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The last bytes of a string. -/
theorem absorbTail_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbTail y) := by
  refine CT.seq (J := fun s => AbsI k w sp R q1 P len s ∧ s.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧
    s.z = decide (len % 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := split15_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h6, hz⟩
  refine CT.ite (decide (len % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len % 16 ≠ 0 := by simpa using hb
  refine CT.assoc (CT.seq (J := Env k w sp R q1) ?_ (fun _ ⟨⟨he, hP, h4, h5⟩, h6, _⟩ => ?_) (updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block (zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
          .mov .r3 (.reg .r6)])) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2, h₂.1.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₃, run₃, -, lp, he₃, -, -, -, -⟩ := tailPre_ok L he hP hl h0 h4 h5 h6
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    exact WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨_, lo⟩ => he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr

/-- A string padded. -/
theorem absorbPad_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (AbsI k w sp R q1 P len) (absorbPad y) :=
  CT.seq (absorbWhole_ct L hR hy hl) (fun _ ⟨he, hP, h4, h5⟩ =>
    WP.mono (absorbWhole_ok L he hR hy hP hl h4 h5) fun _ A => ⟨A.env, fun h => (hP h).of_eq A.rd A.wr, A.r4, A.r5⟩)
    (absorbTail_ct L hR hy hl)

/-- The first block of the associated data. -/
theorem aadHead_ct {y : Nat} (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (fun s => Env k w sp R q1 s ∧ Buf w sp s A a ∧ s.gpr .r4 = A ∧ s.gpr .r5 = BitVec.ofNat 32 a)
      (aadHead y) := by
  refine CT.assoc4 (CT.seq (J := Env k w sp R q1) ?_ (fun s ⟨he, hA, h4, h5⟩ =>
    WP.mono (aadHeadPre_ok L he hA ha0 ha h4 h5) fun _ h => h.1) (updBlock_ct L hR hy))
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r8, .r9, .r10, .r11])
      (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO, .dp .add .r2 .r2 (.reg .r6),
        .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · exact env_eq h₁.1 h₂.1 hr

end

/-- Between the pieces of the MAC: one run, the environment with `q − 1` in
`r10`, and `Ctr₀` at `W + 48`. -/
def MacI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ Env k w sp R (14 - nl) s ∧
    ∃ nonce : List Byte, nonce.length = nl ∧
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

theorem c0_macR {y : Nat} (hy : y = 0 ∨ y = 112) (L : Lay k w sp) {m m' : Mem} (hf : Frame (macR w sp y) m m') :
    bytesAt m' (State.addr w + BitVec.ofNat 64 48) 16 = bytesAt m (State.addr w + BitVec.ofNat 64 48) 16 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- After a piece of the MAC. -/
theorem MacI.next {y : Nat} (hy : y = 0 ∨ y = 112) {s s' : State} (h : MacI k w sp N A D T R nl al n tl s)
    {Y : List Byte} (M : MacStep k w sp R (14 - nl) s y Y s') : MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he, nonce, hl, hc⟩ := h
  have L : Lay k w sp := by have := o.ar.lay; rwa [o.sp] at this
  exact ⟨o.next M.frame (macR_mut hy) (by rw [M.env.sp, he.sp]) M.rd M.wr, M.env, nonce, hl,
    by rw [c0_macR hy L M.frame, hc]⟩

theorem MacI.lay {s : State} (h : MacI k w sp N A D T R nl al n tl s) : Lay k w sp := by
  have := h.1.ar.lay; rwa [h.1.sp] at this

variable (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hal : al < 2 ^ 32)
include L hR hal

/-- The associated data. -/
theorem aad_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (aad y) := by
  refine CT.seq (J := fun s => MacI k w sp N A D T R nl al n tl s ∧ s.gpr .r4 = A ∧
    s.gpr .r5 = BitVec.ofNat 32 al ∧ s.z = decide (al = 0)) ?_ (fun s h => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, hz, g₁, k₁⟩ := aadLd_ok h.1.ar.stk h.1.eA h.1.eal hal
    have he₁ := h.2.1.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
    refine WP.of_runBlock ⟨s₁, run₁, ⟨h.1.next (rs := []) (by rw [k₁.mem]; exact Frame.refl _ _)
      (fun _ h => by simp at h) k₁.sp k₁.rd k₁.wr, he₁, ?_⟩, h4, h5, hz⟩
    obtain ⟨nonce, hl, hc⟩ := h.2.2
    exact ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩
  refine CT.ite (decide (al = 0)) (fun s h => h.2.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : al ≠ 0 := by simpa using hb
  have hn1 : headLen al ≤ al := by unfold headLen; omega_arith
  have bufA : ∀ {s : State}, MacI k w sp N A D T R nl al n tl s → Buf w sp s A al := fun h => by
    have := h.1.ar.aad; rwa [h.1.sp] at this
  refine CT.seq (J := AbsI k w sp R (14 - nl) (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((aadHead_ct L hR hy (by omega_arith) hal).mono fun s ⟨h, h4, h5, _⟩ => ⟨h.2.1, bufA h, h4, h5⟩)
    (fun s ⟨h, h4, h5, _⟩ => WP.mono (aadHead_ok L h.2.1 hR hy (bufA h) (by omega_arith) hal h4 h5) fun _ A₂ =>
      ⟨A₂.env, fun e => ((bufA h).sub (j := headLen al) (k := al - headLen al) (by omega_arith) (by omega_arith)).of_eq
        A₂.rd A₂.wr, A₂.r4, A₂.r5⟩) (absorbPad_ct L hR hy (by omega_arith))

/-- `B₀`. -/
theorem b0_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (b0 y) := by
  refine CT.assoc (CT.seq (J := Env k w sp R (14 - nl)) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) (updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r8, .r9, .r10, .r11] (4 * 7))
        (.seq flagsCode (.block (b0Block y))) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.args _ (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, hc⟩
  · have Ar := o.ar
    exact WP.mono (b0Pre_ok L he Ar.stk o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ h => h.1

/-- The MAC. -/
theorem mac_ct {y : Nat} (hy : y = 0 ∨ y = 112) (hn : n < 2 ^ 32) : CT (MacI k w sp N A D T R nl al n tl) (mac y) := by
  refine CT.seq (J := MacI k w sp N A D T R nl al n tl) (b0_ct L hR hal hy) (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · have Ar := o.ar
    exact WP.mono (b0_ok L he Ar.stk hR o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ M => MacI.next hy ⟨o, he, nonce, hl, hc⟩ M
  refine CT.seq (J := MacI k w sp N A D T R nl al n tl) (aad_ct L hR hal hy) (fun s h => ?_) ?_
  · obtain ⟨o, he, _⟩ := id h
    have bufA : Buf w sp s A al := by have := o.ar.aad; rwa [o.sp] at this
    exact WP.mono (aad_ok L he hR hy o.ar.stk o.eA o.eal hal bufA) fun _ M => MacI.next hy h M
  refine CT.seq (J := AbsI k w sp R (14 - nl) D n) ?_ (fun s ⟨o, he, _⟩ => ?_) (absorbPad_ct L hR hy hn)
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := dataLd_ok o.ar.stk o.eD o.en
    have bufD : Buf w sp s D n := by have := o.ar.data.buf; rwa [o.sp] at this
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      fun _ => bufD.of_eq k₁.rd k₁.wr, h4, h5⟩

end

end VG.Proof.AesCcm.Arm
