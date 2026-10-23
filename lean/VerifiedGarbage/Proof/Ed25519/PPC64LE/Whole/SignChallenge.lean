module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignNonce
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignExpand

/-!
# `vg_ed25519_sign_cached` on PPC64LE: the challenge, and `S`

`R` (in `out`), the copy of `pk` at `192(F)` and the message hashed into
`128(F)`, the digest reduced into the challenge at `96(F)` by a call of
`vg_ed25519_scalar_reduce`, and `S = (r + k s) mod L` into `out + 32` by a
call of `vg_ed25519_scalar_mul_add` (`signChallenge_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- What the challenge's steps write. -/
abbrev chW (s : State) : List Region :=
  [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, below s.sp 48, ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩]

theorem signChallenge_ok (C : ShaOK) {s t : State} (hp : SignPre s) (h : SignInv s t) {Rb Nb Sb Kb : List Byte}
    (hR : bytesAt t.mem (s.gpr .r3) 32 = Rb) (hN : bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 64) 32 = Nb)
    (hS : bytesAt t.mem (s.gpr .r9) 32 = Sb) (hK : bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = Kb) :
    WP isa signChallenge t fun t' => SignInv s t' ∧ bytesAt t'.mem (s.gpr .r3) 32 = Rb ∧
      bytesAt t'.mem (s.gpr .r3 + BitVec.ofNat 64 32) 32 =
        Spec.Ed25519.scalarMulAdd Nb (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s))) Sb := by
  have hRl : Rb.length = 32 := by rw [← hR]; simp [bytesAt]
  have hKl : Kb.length = 32 := by rw [← hK]; simp [bytesAt]
  have hlen := sign_len hp
  have toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .r8, 8192⟩, below sp 48] m m' →
      Frame (chW s) m m' := fun e hf => by subst e; exact hf.mono (by simp)
  have scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .r8, 8192⟩ : Region), below t.sp 48], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  have F0 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 0, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F64 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F96 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F128 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F192 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have O32 : Region.Sub ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r3, 64⟩ := Region.sub_prefix (by decide)
  have O32' : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .r3, 64⟩ := Offset.sub_base _ (by decide)
  -- What the steps keep.
  have keep : ∀ {m m' : Mem} {p : Addr}, Frame (chW s) m m' → Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt m' p 32 = bytesAt m p 32 := by
    intro m m' p hf hpr
    refine bytes_keep hf (by decide) fun r hr => ?_
    have hF : Region.Sub ⟨p, 32⟩ ⟨s.gpr .r9, 288⟩ ∨ Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ := by
      rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact .inr h
      · exact .inl (Offset.sub_base _ (by omega))
      · exact .inl F192
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hF with hF | hF
      · exact hp.cF.symm.sub_left hF
      · exact (hp.oC.sub_left O32).sub_left hF
    · rcases hpr with h | ⟨d, hd, rfl⟩ | rfl
      · exact (hp.oF.sub_left O32).sub_left h |>.sub_right (Offset.sub_base _ (by decide))
      · exact Offset.disjoint _ (.inl hd) (by omega) (by decide)
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · rcases hF with hF | hF
      · exact hp.bF.symm.sub_left hF
      · exact (hp.bO.symm.sub_left O32).sub_left hF
    · rcases hF with hF | hF
      · exact hp.oF.symm.sub_left hF |>.sub_right O32'
      · exact ((Offset.base_disjoint _ (by decide) (by decide) : Region.Disjoint ⟨s.gpr .r3, 32⟩
          ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩)).sub_left hF
  have kR : ∀ {m m' : Mem}, Frame (chW s) m m' → bytesAt m' (s.gpr .r3) 32 = bytesAt m (s.gpr .r3) 32 :=
    fun hf => keep hf (.inl fun _ h => h)
  have kF : ∀ {m m' : Mem} {d : Nat}, Frame (chW s) m m' → d + 32 ≤ 96 →
      bytesAt m' (s.gpr .r9 + BitVec.ofNat 64 d) 32 = bytesAt m (s.gpr .r9 + BitVec.ofNat 64 d) 32 :=
    fun hf hd => keep hf (.inr (.inl ⟨_, hd, rfl⟩))
  unfold signChallenge
  refine WP.seq (hashInit_ok C (sr := .r24) (by decide) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ => ?_)
  have h₂ := signStep hp h a b c g f₂ (scW h)
  have hOw : (⟨s.gpr .r3, 64⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r20) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₂.rd, h₂.wr]
      exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩)
    (hp.oC.sub_left O32) (by rw [h₂.sp]; exact hp.bO.sub_right O32) fun t₃ a b c f₃ g hr₃ => ?_)
  have h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  have e₂ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₂.mem p 32 = bytesAt t.mem p 32 := fun hpr => keep (toL h.sp f₂) hpr
  have r₃ : Repr t₃.mem (s.gpr .r8) Rb := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, e₂ (.inl fun _ h => h), hR] at this
  have e₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₃.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₂.sp f₃) hpr).trans (e₂ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r25) (off := 192) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₃), 192, rfl, show 192 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  have h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  have r₄ : Repr t₄.mem (s.gpr .r8) (Rb ++ Kb) := by
    have := hr₄ Rb r₃ (by rw [hRl])
    rwa [e₃ (.inr (.inr rfl)), hK] at this
  have e₄ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₄.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₃.sp f₄) hpr).trans (e₃ hpr)
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r22) (off := 0) (len := (s.gpr .r7).toNat) (by decide)
    (by decide) (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 64) (by decide)) (Sets.addi (d := .r6) (n := .r23) (k := 0) (by decide) (by decide))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .r23 (by decide) (by decide) (by decide)])
    (by rw [BitVec.add_zero, h₄.regs _ (by decide)]; rfl) (sign_env hp h₄) (sign_msg_cov hp h₄)
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  have h₅ := signStep hp h₄ a b c g f₅ (scW h₄)
  have r₅ : Repr t₅.mem (s.gpr .r8) (Rb ++ Kb ++ msgB s) := by
    have := hr₅ (Rb ++ Kb) r₄ (by rw [List.length_append, hRl, hKl])
    rwa [sign_msg hp h₄] at this
  have e₅ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₅.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep (toL h₄.sp f₅) hpr).trans (e₄ hpr)
  refine WP.seq (hashFinalize_ok C (sr := .r24) (f := .r25) (o := 128) (out := s.gpr .r9 + BitVec.ofNat 64 128)
    (vc := fun g => g .r23 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .r4) (n := .r23) (k := 64) (by decide) (by decide)) (fun g g' hg => by rw [hg .r23 (by decide)])
    (sign_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₅, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₅.sp]; exact hp.bF.sub_right F128) fun t₆ a b c f₆ g hd₆ => ?_)
  have h₆ := signStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₅.sp])))
  have dg : bytesAt t₆.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (Rb ++ Kb ++ msgB s) :=
    hd₆ _ r₅ (by rw [List.length_append, List.length_append, hRl, hKl, msgB_length]; omega)
      (by rw [h₅.regs _ (by decide), List.length_append, List.length_append, hRl, hKl, msgB_length, cnt_eq]; rfl)
  have f₆' : Frame (chW s) t₅.mem t₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, by simp,
        Offset.sub (s.gpr .r9) (d := 128) (n := 64) (e := 96) (k := 96) (by decide) (by decide)⟩
    · exact ⟨below s.sp 48, by simp, by rw [h₅.sp]; exact fun _ h => h⟩
  have e₆ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₆.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₆' hpr).trans (e₅ hpr)
  have ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hFw := sign_Fw hp h₆
  have hCw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ t₆.wr := (sign_env hp h₆).w
  -- The challenge: `scalar_reduce`.
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), signV_r25] at c3 c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, signV_r24] at c5
  refine WP.seq (WP.call (k := reducePPC) reduce_ok' (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .r8, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  have h₈ := signStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨96, 32, by decide, rfl⟩))))
      · exact .inl rfl
  have f₈' : Frame (chW s) t₆.mem t₈.mem := by
    rw [← k₇.mem]
    exact f₈.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .r9 + BitVec.ofNat 64 96, 96⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  have e₈ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r3, 32⟩ ∨
      (∃ d, d + 32 ≤ 96 ∧ p = s.gpr .r9 + BitVec.ofNat 64 d) ∨ p = s.gpr .r9 + BitVec.ofNat 64 192 →
      bytesAt t₈.mem p 32 = bytesAt t.mem p 32 := fun hpr => (keep f₈' hpr).trans (e₆ hpr)
  -- `S`: `scalar_mul_add`.
  refine WP.seq (args5_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun t₉ k₉ d3 d4 d5 d6 d7 => ?_)
  rw [h₈.regs _ (by decide), signV_r20] at d3
  rw [h₈.regs _ (by decide), signV_r25] at d4 d5
  rw [h₈.regs _ (by decide), signV_r25, BitVec.add_zero] at d6
  rw [h₈.regs _ (by decide), signV_r24, BitVec.add_zero] at d7
  have hOw' : (⟨s.gpr .r3, 64⟩ : Region) ∈ t₉.wr := by rw [k₉.wr, h₈.wr, hp.wr]; simp
  have hFw' : (⟨s.gpr .r9, 288⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact sign_Fw hp h₈
  have hCw' : (⟨s.gpr .r8, 8192⟩ : Region) ∈ t₉.wr := by rw [k₉.wr]; exact (sign_env hp h₈).w
  refine WP.call (k := mulAddPPC) mulAdd_ok'
    (rd := [⟨s.gpr .r9 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .r9 + BitVec.ofNat 64 96, 32⟩, ⟨s.gpr .r9, 32⟩])
    (wr := [⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩, ⟨s.gpr .r8, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), ce _ _ (by decide), ce _ _ (by decide), d4, d5, d6],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), d3, d7],
      by rw [ce _ _ (by decide), ce _ _ (by decide), d3, d7]; exact hp.oC.sub_left O32',
      by rw [ce _ _ (by decide), ce _ _ (by decide), d4, d7]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d5, d7]; exact hp.cF.symm.sub_left F96,
      by rw [ce _ _ (by decide), ce _ _ (by decide), d6, d7]
         exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))⟩
    (Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw', 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 96, rfl, show 96 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw', 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw', 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw', 32, rfl, show 32 + 32 ≤ 64 by decide⟩
      · exact ⟨_, hCw', 0, by simp, by simp⟩) (fun t₁₀ a b c f₁₀ g _ hpost' => ?_) (by decide +kernel)
  simp only [mulAddPPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    d3, d4, d5, d6, k₉.mem] at hpost'
  have h₁₀ := signStep hp h₈ (a.trans k₉.rd) (b.trans k₉.wr) (c.trans k₉.sp)
    (fun r hr => (g r hr).trans (k₉.pres r hr)) (k₉.mem ▸ f₁₀) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inl rfl)))
      · exact .inl rfl
  have f₁₀' : Frame (chW s) t₈.mem t₁₀.mem := by
    rw [← k₉.mem]
    exact f₁₀.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₁₀, by rw [kR f₁₀', e₈ (.inl fun _ h => h), hR], ?_⟩
  rw [hpost', e₈ (.inr (.inl ⟨64, by decide, rfl⟩)), hN, hpost,
    show s.gpr .r9 = s.gpr .r9 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, e₈ (.inr (.inl ⟨0, by decide, rfl⟩)),
    ← show s.gpr .r9 = s.gpr .r9 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm, hS]

end VG.Proof.Ed25519.PPC64LE.Whole
