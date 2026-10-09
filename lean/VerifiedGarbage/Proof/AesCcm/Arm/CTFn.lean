import VerifiedGarbage.Proof.AesCcm.Arm.CTCrypt

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal` and `vg_aes_ccm_open` are constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments (`onePub`) both satisfy the invariants of the same
public values (`entryI`), piece by piece. `open` compares the tags and masks
the data without a branch: whether the tag is right, in `r0` and `r7`, is
never branched on nor used as an address.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI recv cmp uO restore)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame savedR)
open VG.Proof.AesCcm (length_bytesAt)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Counter mode. -/
theorem ctr_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (MacI k w sp N A D T R nl al n tl) ctr := by
  refine CT.seq (J := CrI k w sp R nl D n) ?_ (fun s ⟨o, he, c0⟩ => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := dataLd_ok o.ar.stk o.eD o.en
    have hD : Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
    obtain ⟨nonce, hl, hc⟩ := c0
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩, hD.of_eq k₁.rd k₁.wr, h4, h5⟩
  refine CT.seq (J := CrI k w sp R nl D n) (ctrWhole_ct L hR h7 h13 hn4) (fun s ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ => ?_)
    (ctrTail_ct L hR h7 h13 hn hn4)
  refine WP.mono (ctrWhole_ok L he hR (nonce := nonce) (by omega_arith) (by omega_arith) hc hD (by rw [hl]; exact hn) hn4 h4 h5)
    fun s' ⟨he', rd, wr, g, f, _⟩ => ⟨he', ⟨nonce, hl, ?_⟩, hD.of_eq rd wr, by rw [g _ (by decide) (by decide), h4],
      by rw [g _ (by decide) (by decide), h5]⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact ((hD.buf.w.sub_left (Region.sub_prefix (Nat.mul_div_le n 16))).sub_right
        (Lay.wSub (by decide))).symm) (by decide), hc]

end

/-- At the entry: one run, and the registers holding the key schedule, the
rounds and the nonce. -/
def EntI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ s.gpr .r0 = k ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

/-- After the entry. -/
def AftI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  One k w sp N A D T R nl al n tl s ∧ Env k w sp R (s.gpr .r10).toNat s ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)

/-- The entry. -/
theorem entry_ct : CT (EntI k w sp N A D T R nl al n tl) (.block entry) :=
  CT.args [.r0, .r1, .r2, .r3] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2, h₂.2.2.2.2]) ⟨_, by taint_decide⟩

theorem entry_wpI {s : State} (h : EntI k w sp N A D T R nl al n tl s) :
    WP isa (.block entry) s (AftI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, h0, h1, h2, h3⟩ := h
  refine WP.mono (entry_wp o.ar h0 h1 o.eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, _, f₁⟩ => ?_
  have hsp : s₁.sp = s.sp := he₁.sp
  rw [o.sp] at he₁
  refine ⟨o.next' f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact o.ar.stk.aw.sub_right (Lay.wSub (by decide)))
    hsp rd₁ wr₁, he₁, by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2],
    by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]⟩

/-- `Ctr₀`. -/
theorem ctrs_ct : CT (AftI k w sp N A D T R nl al n tl) ctrs :=
  CT.args [.r2, .r3, .r8, .r9, .r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1.r8, h₂.2.1.r8]
    · rw [h₁.2.1.r9, h₂.2.1.r9]
    · rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

include L in
theorem ctrs_wpI {s : State} (h : AftI k w sp N A D T R nl al n tl s) :
    WP isa ctrs s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, h2, h3⟩ := h
  have hN : Buf w sp s N nl := by have := o.ar.nonce; rwa [o.sp] at this
  refine WP.mono (ctrs_ok L he hN h2 h3 o.ar.h7 o.ar.h13) fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  refine ⟨o.next f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_mut (.inl (by decide))) sp₂ rd₂ wr₂,
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r11],
      by rw [sp₂, he.sp], he.perm.of_eq rd₂ wr₂⟩, _, length_bytesAt _ _ _, c₂⟩

include L hR

theorem mac_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa (mac y) s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have Ar := o.ar
  have hA : Buf w sp s A al := by have := Ar.aad; rwa [o.sp] at this
  have hD : Buf w sp s D n := by have := Ar.data.buf; rwa [o.sp] at this
  exact WP.mono (mac_ok L he Ar.stk o.sp hR o.eA o.eal o.eD o.en o.etl hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32
    Ar.n32 Ar.hn hc hy hA hD) fun _ M => MacI.next hy h M

theorem tag_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa (tag y) s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  refine WP.mono (tag_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13) hc hy)
    fun s' ⟨he', rd, wr, _, f, _⟩ => h.of he' f (fun r hr => ?_) (fun r hr => ?_) rd wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_mut (.inl (by decide))
    · exact w_mut (.inl (by omega_arith))
    · exact w_mut (.inr ⟨by decide, by decide⟩)
    · exact blw_mut
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm

theorem ctr_wpI {s : State} (h : MacI k w sp N A D T R nl al n tl s) :
    WP isa ctr s (MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have hD : Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
  refine WP.mono (ctr_ok L he o.ar.stk hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13)
    hc o.eD o.en hD (by rw [hl]; exact o.ar.hn) o.ar.n32) fun s' ⟨he', rd, wr, _, f, _⟩ =>
      h.of he' f ctrR_mut (fun r hr => ?_) rd wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.buf.w.sub_right (Lay.wSub (by decide))).symm

/-- `vg_aes_ccm_seal`, from the entry invariant. -/
theorem seal_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (EntI k w sp N A D T R nl al n tl) «seal» := by
  refine CT.seq entry_ct (fun _ h => entry_wpI h) ?_
  refine CT.seq ctrs_ct (fun _ h => ctrs_wpI L h) ?_
  refine CT.seq (mac_ct L hR hal (.inl rfl) hn4) (fun _ h => mac_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (tag_ct L hR (.inl rfl)) (fun _ h => tag_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (ctr_ct L hR h7 h13 hn hn4) (fun _ h => ctr_wpI L hR h) ?_
  -- The copy of the tag to `tag`, a public stack argument, and the exit.
  exact CT.args [.r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open`, from the entry invariant. -/
theorem open_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (EntI k w sp N A D T R nl al n tl) «open» := by
  refine CT.seq entry_ct (fun _ h => entry_wpI h) ?_
  refine CT.seq ctrs_ct (fun _ h => ctrs_wpI L h) ?_
  refine CT.seq (ctr_ct L hR h7 h13 hn hn4) (fun _ h => ctr_wpI L hR h) ?_
  refine CT.seq (mac_ct L hR hal (.inr rfl) hn4) (fun _ h => mac_wpI L hR (.inr rfl) h) ?_
  refine CT.seq (tag_ct L hR (.inr rfl)) (fun _ h => tag_wpI L hR (.inr rfl) h) ?_
  exact CT.args [.r8, .r9, .r10, .r11] (fun s h => h.1.pubArgs)
    (fun s₁ s₂ h₁ h₂ r hr => env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, by taint_decide⟩

end

end VG.Proof.AesCcm.Arm
