import VerifiedGarbage.Proof.AesCcm.Arm.CTMac

/-!
# AES-CCM on ARMv7: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`
get the same arguments in both runs (`Proof.AesGcm.Arm.CT.ctr`); the
branches are on the length of the data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 xorLoop ctrFrame)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame ctr_call CtrCall)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

/-- After code that writes `rs`, within what the pieces write and apart from `Ctr₀`. -/
theorem MacI.of {s s' : State} (h : MacI k w sp N A D T R nl al n tl s) (he : Env k w sp R (14 - nl) s')
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ mutR w sp D n, Region.Sub r r')
    (hd : ∀ r ∈ rs, (⟨State.addr w + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he₀, nonce, hl, hc⟩ := h
  exact ⟨o.next hf hsub (by rw [he.sp, he₀.sp]) hrd hwr, he, nonce, hl, by rw [bytesAt_frame hf hd (by decide), hc]⟩

variable (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `tag y`. -/
theorem tag_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (MacI k w sp N A D T R nl al n tl) (tag y) := by
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 y)
    (w + BitVec.ofNat 32 384) R 1 ∧ s.sp = sp) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 0)] ++ ctrAt ++ ctrArgs ++ [addI .r3 .r11 y, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) hc
  · obtain ⟨s₃, run₃, C, he₃, -⟩ := tagArgs_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7)
      (by rw [hl]; exact o.ar.h13) hc hy
    exact WP.of_runBlock ⟨s₃, run₃, C, he₃.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- Before counter mode. -/
def CrI (k w sp : BitVec 32) (R nl : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop :=
  Env k w sp R (14 - nl) s ∧ (∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) ∧
  Dat k w sp s D n ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n

omit L hR in
theorem CrI.keep {s s' : State} (h : CrI k w sp R nl D n s) (hg : ∀ r, r ≠ .r12 → r ≠ .r6 → s'.gpr r = s.gpr r)
    (hk : Proof.AesGcm.Arm.Keeps s s') : CrI k w sp R nl D n s' := by
  obtain ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ := h
  exact ⟨he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    ⟨nonce, hl, by rw [hk.mem]; exact hc⟩, hD.of_eq hk.rd hk.wr, by rw [hg _ (by decide) (by decide), h4],
    by rw [hg _ (by decide) (by decide), h5]⟩

/-- The whole blocks of the data. -/
theorem ctrWhole_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn4 : n < 2 ^ 32) : CT (CrI k w sp R nl D n) ctrWhole := by
  refine CT.seq (J := fun s => CrI k w sp R nl D n s ∧ s.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧
    s.z = decide (n / 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := split16_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r a _ => g₁ r a) k₁, h12, hz⟩
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R (n / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, hD, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)])) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₄, run₄, C, he₄, -⟩ := ctrWholeArgs_ok L he hR (nonce := nonce) (by omega_arith) (by omega_arith) hc hD h4 h12
    exact WP.of_runBlock ⟨s₄, run₄, C, he₄.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- The last bytes of the data. -/
theorem ctrTail_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (CrI k w sp R nl D n) ctrTail := by
  refine CT.seq (J := fun s => CrI k w sp R nl D n s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.z = decide (n % 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := split15_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r _ b => g₁ r b) k₁, h6, hz⟩
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  let J₃ : State → Prop := fun s => Env k w sp R (14 - nl) s ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n ∧
    s.gpr .r6 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 80)
      (w + BitVec.ofNat 32 384) R 1 ∧ J₃ s) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, _, h4, h5⟩, h6, _⟩ => ?_)
    (CT.seq (J := J₃) ?_ (fun s ⟨C, he, h4, h5, h6⟩ => WP.mono (ctr_call C) fun s' P =>
      ⟨he.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h4],
        by rw [P.saved _ (by decide) (by decide), h5], by rw [P.saved _ (by decide) (by decide), h6]⟩) ?_)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r8, .r9, .r10, .r11])
        (.block (zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
          [addI .r3 .r11 ksO, .mov .r12 (imm 1)])) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.2, h₂.1.2.2.2.2]
    · exact env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₅, run₅, C, he₅, g₅, -⟩ := ctrTailArgs_ok L he hR (nonce := nonce) (by omega_arith) (by omega_arith) hc
      (by rw [hl]; exact hn) hn4 h5
    exact WP.of_runBlock ⟨s₅, run₅, C, he₅, by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h4], by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h5],
      by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.1.sp.trans e₂.1.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6), .dp .add .r2 .r2 (.reg .r4),
          .mov .r3 (.reg .r6)]) xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · exact env_eq h₁.1 h₂.1 hr

end

end VG.Proof.AesCcm.Arm
