module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Challenge
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed25519_verify` on PPC64LE: the challenge

`pk` in `r3`, the message in `r4` (`len` in `r5`), the signature in `r6`,
`scratch` in `r7` and the frame `F` (192 bytes) in `r8`. The registers saved
at `128(F)`, `R ‖ A ‖ M` hashed into `64(F)`, the digest reduced into `0(F)`
by a call of `vg_ed25519_scalar_reduce` and its upper half zeroed, and the
arguments of `verify_equation` set (`verifyHash_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- The message. -/
abbrev vmsgR (s : State) : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩

/-- The precondition, by register. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 32⟩, vmsgR s, ⟨s.gpr .r6, 64⟩]
  wr : s.wr = [⟨s.gpr .r7, 8192⟩, ⟨s.gpr .r8, 192⟩]
  pC : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r7, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r8, 192⟩
  mC : Region.Disjoint (vmsgR s) ⟨s.gpr .r7, 8192⟩
  mF : Region.Disjoint (vmsgR s) ⟨s.gpr .r8, 192⟩
  sC : Region.Disjoint ⟨s.gpr .r6, 64⟩ ⟨s.gpr .r7, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r6, 64⟩ ⟨s.gpr .r8, 192⟩
  cF : Region.Disjoint ⟨s.gpr .r7, 8192⟩ ⟨s.gpr .r8, 192⟩
  sp : 48 ≤ s.sp.toNat
  bP : (below s.sp 48).Disjoint ⟨s.gpr .r3, 32⟩
  bM : (below s.sp 48).Disjoint (vmsgR s)
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r6, 64⟩
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r7, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r8, 192⟩

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [⟨s.gpr .r7, 8192⟩, ⟨s.gpr .r8, 192⟩, below s.sp 48]

/-- The values in `r20`–`r25`. -/
def verV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r5 | .r23 => s.gpr .r6 | .r24 => s.gpr .r7
  | .r25 => s.gpr .r8 | _ => 0

abbrev VerInv (s : State) : State → Prop := Inv s (s.gpr .r8) 128 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

theorem verV_r20 (s : State) : verV s .r20 = s.gpr .r3 := rfl
theorem verV_r21 (s : State) : verV s .r21 = s.gpr .r4 := rfl
theorem verV_r22 (s : State) : verV s .r22 = s.gpr .r5 := rfl
theorem verV_r23 (s : State) : verV s .r23 = s.gpr .r6 := rfl
theorem verV_r24 (s : State) : verV s .r24 = s.gpr .r7 := rfl
theorem verV_r25 (s : State) : verV s .r25 = s.gpr .r8 := rfl

/-- The regions a step may write: the scratch space, the callees' frames, or the frame below the
slots. -/
def VerWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .r7, 8192⟩ ∨ r = below s.sp 48 ∨ ∃ d n, d + n ≤ 128 ∧ r = ⟨s.gpr .r8 + BitVec.ofNat 64 d, n⟩

theorem verStep {s t t' : State} (hp : VerPre s) (h : VerInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, VerWr s r) : VerInv s t' := by
  have hs : Region.Sub (slotArea (s.gpr .r8) 128 verifyRegs) ⟨s.gpr .r8, 192⟩ := Offset.sub_base _ (by decide)
  refine Inv.step h verifyRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r8, 192⟩, by simp, Offset.sub_base _ (by omega)⟩
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs
    · exact Offset.disjoint _ (.inr hdn) (by decide) (by omega)

/-- An input, while the body runs. -/
theorem ver_input {s t : State} (h : VerInv s t) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hC : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r7, 8192⟩) (hF : Region.Disjoint ⟨p, n⟩ ⟨s.gpr .r8, 192⟩)
    (hB : Region.Disjoint ⟨p, n⟩ (below s.sp 48)) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame hn fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hC
    · exact hF
    · exact hB

theorem ver_env {s t : State} (hp : VerPre s) (h : VerInv s t) : ScEnv (s.gpr .r7) t :=
  ⟨by rw [h.wr, hp.wr]; simp, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

theorem ver_Fw {s t : State} (hp : VerPre s) (h : VerInv s t) : (⟨s.gpr .r8, 192⟩ : Region) ∈ t.wr := by
  rw [h.wr, hp.wr]; simp

/-- The setup: the registers saved, the pointers moved to `r20`–`r25`. -/
theorem verSetup_ok {s : State} (hp : VerPre s) :
    WP isa (.block (saveRegs .r8 128 verifyRegs ++
      [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6, mov .r24 .r7, mov .r25 .r8])) s (VerInv s) := by
  have hF : (⟨s.gpr .r8, 192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 128 verifyRegs, p.2 + 8 ≤ 192 := by decide
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu _ hsv hfr => ?_
  unfold mov
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ =>
    wp_addi (by decide) (by decide) fun u₅ h₅ => wp_addi (by decide) (by decide) fun u₆ h₆ => WP.block_nil ?_
  have m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g₆ : ∀ r, r ∉ verifyRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  have gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
  refine ⟨by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd],
    by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr],
    by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp], fun r hr => ?_, fun r hr hn => ?_, m₆ ▸ hsv,
    m₆ ▸ (hfr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨⟨s.gpr .r8, 192⟩, by simp, Offset.sub_base _ (by decide)⟩)⟩
  · simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.gpr, BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.gpr, h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr,
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.other _ (by decide), h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
    · rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
        h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]; rfl
  · rw [g₆ r hn, gu r fun e => r0_pres (e ▸ hr)]

/-- The message's bytes, and `verify`'s challenge. -/
abbrev vmsgB (s : State) : List Byte := bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat

abbrev vChallenge (s : State) : List Byte :=
  Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE (Spec.Sha512.sha512
    (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s)) % Spec.Ed25519.L)

/-- After the challenge: the arguments of `verify_equation`. -/
structure VerArgs (s t : State) : Prop where
  inv : VerInv s t
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r8
  r6 : t.gpr .r6 = s.gpr .r7
  ch : bytesAt t.mem (s.gpr .r8) 64 = vChallenge s

theorem verifyHash_ok (C : ShaOK) {s : State} (hp : VerPre s) : WP isa verifyHash s (VerArgs s) := by
  have hlen : (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64 := len_add_le (Nat.le_of_lt (s.gpr .r5).isLt) (by decide) hp.mC
  have scW : ∀ {t : State}, VerInv s t → ∀ r ∈ [(⟨s.gpr .r7, 8192⟩ : Region), below t.sp 48], VerWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  have S32 : Region.Sub ⟨s.gpr .r6, 32⟩ ⟨s.gpr .r6, 64⟩ := Region.sub_prefix (by decide)
  have F0 : Region.Sub ⟨s.gpr .r8, 32⟩ ⟨s.gpr .r8, 192⟩ := Region.sub_prefix (by decide)
  have F64 : Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 64, 64⟩ ⟨s.gpr .r8, 192⟩ := Offset.sub_base _ (by decide)
  have inRd : ∀ {t : State}, VerInv s t → ∀ {r : Region}, r ∈ s.rd → Covers [r] (t.rd ++ t.wr) :=
    fun h r hr a n hi => by
      obtain ⟨r', hr', hc⟩ := hi
      rw [List.mem_singleton.mp hr'] at hc
      exact ⟨r, List.mem_append_left _ (by rw [h.rd]; exact hr), hc⟩
  unfold verifyHash
  refine WP.seq (WP.mono (verSetup_ok hp) fun t₁ h₁ => ?_)
  refine WP.seq (hashInit_ok C (sr := .r24) (by decide) (h₁.regs _ (by decide)) (ver_env hp h₁)
    fun t₂ a b c f₂ g hr₂ => ?_)
  have h₂ := verStep hp h₁ a b c g f₂ (scW h₁)
  -- `R`, the signature's first half.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r23) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₂.rd, hp.rd]
      exact ⟨⟨s.gpr .r6, 64⟩, by simp, 0, by simp, by simp⟩)
    (hp.sC.sub_left S32) (by rw [h₂.sp]; exact hp.bS.sub_right S32) fun t₃ a b c f₃ g hr₃ => ?_)
  have h₃ := verStep hp h₂ a b c g f₃ (scW h₂)
  have r₃ : Repr t₃.mem (s.gpr .r7) (bytesAt s.mem (s.gpr .r6) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, ver_input h₂ (by decide) (hp.sC.sub_left S32) (hp.sF.sub_left S32)
      (hp.bS.symm.sub_left S32)] at this
  -- `A`.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r20) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₃) (inRd h₃ (by rw [hp.rd]; simp))
    hp.pC (by rw [h₃.sp]; exact hp.bP) fun t₄ a b c f₄ g hr₄ => ?_)
  have h₄ := verStep hp h₃ a b c g f₄ (scW h₃)
  have r₄ : Repr t₄.mem (s.gpr .r7) (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32) := by
    have := hr₄ _ r₃ (by simp [bytesAt])
    rwa [ver_input h₃ (by decide) hp.pC hp.pF hp.bP.symm] at this
  -- The message.
  refine WP.seq (hashUpdate_ok C (sr := .r24) (src := .r21) (off := 0) (len := (s.gpr .r5).toNat) (by decide)
    (by decide) (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 64) (by decide)) (Sets.addi (d := .r6) (n := .r22) (k := 0) (by decide) (by decide))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .r22 (by decide) (by decide) (by decide)])
    (by rw [BitVec.add_zero, h₄.regs _ (by decide)]; rfl) (ver_env hp h₄) (inRd h₄ (by rw [hp.rd]; simp))
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  have h₅ := verStep hp h₄ a b c g f₅ (scW h₄)
  have r₅ : Repr t₅.mem (s.gpr .r7)
      (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s) := by
    have := hr₅ _ r₄ (by simp [bytesAt])
    rwa [ver_input h₄ (s.gpr .r5).isLt hp.mC hp.mF hp.bM.symm] at this
  refine WP.seq (hashFinalize_ok C (sr := .r24) (f := .r25) (o := 64) (out := s.gpr .r8 + BitVec.ofNat 64 64)
    (vc := fun g => g .r22 + BitVec.ofNat 64 64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (h₅.regs _ (by decide))
    (by rw [h₅.regs _ (by decide)]; rfl)
    (Sets.addi (d := .r4) (n := .r22) (k := 64) (by decide) (by decide)) (fun g g' hg => by rw [hg .r22 (by decide)])
    (ver_env hp h₅)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, ver_Fw hp h₅, 64, rfl, show 64 + 64 ≤ 192 by decide⟩)
    (hp.cF.symm.sub_left F64) (by rw [h₅.sp]; exact hp.bF.sub_right F64) fun t₆ a b c f₆ g hd₆ => ?_)
  have h₆ := verStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨64, 64, by decide, rfl⟩)
    · exact .inr (.inl (by rw [h₅.sp])))
  have dg : bytesAt t₆.mem (s.gpr .r8 + BitVec.ofNat 64 64) 64 =
      Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .r6) 32 ++ bytesAt s.mem (s.gpr .r3) 32 ++ vmsgB s) :=
    hd₆ _ r₅ (by simp [bytesAt]; omega)
      (by rw [h₅.regs _ (by decide), cnt_eq, verV_r22]; simp [bytesAt]; congr 1; omega)
  -- `scalar_reduce`.
  have ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hFw := ver_Fw hp h₆
  have hCw : (⟨s.gpr .r7, 8192⟩ : Region) ∈ t₆.wr := (ver_env hp h₆).w
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun t₇ k₇ c3 c4 c5 => ?_)
  rw [h₆.regs _ (by decide), verV_r25, BitVec.add_zero] at c3
  rw [h₆.regs _ (by decide), verV_r25] at c4
  rw [h₆.regs _ (by decide), BitVec.add_zero, verV_r24] at c5
  refine WP.seq (WP.call (k := reducePPC) reduce_ok' (rd := [⟨s.gpr .r8 + BitVec.ofNat 64 64, 64⟩])
    (wr := [⟨s.gpr .r8, 32⟩, ⟨s.gpr .r7, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact Offset.base_disjoint _ (by decide) (by decide),
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F0,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F64⟩
    (Covers.of_sub fun r hr => by
      rw [k₇.rd, k₇.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 64 ≤ 192 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₇.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 0, by simp, by simp⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₈ a b c f₈ g _ hpost => ?_) (by decide +kernel))
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4, k₇.mem, dg] at hpost
  have h₈ := verStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr ⟨0, 32, by decide, by simp⟩)
      · exact .inl rfl
  -- The upper half zeroed, and the arguments.
  have hFw₈ : (⟨s.gpr .r8, 192⟩ : Region) ∈ t₈.wr := ver_Fw hp h₈
  have e25 : t₈.gpr .r25 = s.gpr .r8 := h₈.regs _ (by decide)
  have inF : ∀ (u : State), u.wr = t₈.wr → ∀ d, d + 8 ≤ 192 → InRegions u.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    fun u hu d hd => by rw [hu]; exact in_base hFw₈ hd (by omega)
  refine wp_li (d := .r8) (imm := 0) (by decide) fun u₁ e₁ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 32) (by decide) ⟨by decide, by decide⟩
    (by rw [e₁.other _ (by decide), e25]) (inF _ e₁.wr 32 (by decide)) fun u₂ e₂ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 40) (by decide) ⟨by decide, by decide⟩
    (by rw [e₂.gpr, e₁.other _ (by decide), e25]) (inF _ (by rw [e₂.wr, e₁.wr]) 40 (by decide)) fun u₃ e₃ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 48) (by decide) ⟨by decide, by decide⟩
    (by rw [e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25]) (inF _ (by rw [e₃.wr, e₂.wr, e₁.wr]) 48 (by decide))
    fun u₄ e₄ => ?_
  refine wp_stdd (a := s.gpr .r8 + BitVec.ofNat 64 56) (by decide) ⟨by decide, by decide⟩
    (by rw [e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25])
    (inF _ (by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]) 56 (by decide)) fun u₅ e₅ => ?_
  refine wp_addi (by decide) (by decide) fun v₁ g₁ => wp_addi (by decide) (by decide) fun v₂ g₂ =>
    wp_addi (by decide) (by decide) fun v₃ g₃ => wp_addi (by decide) (by decide) fun v₄ g₄ => WP.block_nil ?_
  have z₁ : u₁.gpr .r8 = 0 := e₁.gpr
  have z₂ : u₂.gpr .r8 = 0 := by rw [e₂.gpr, z₁]
  have z₃ : u₃.gpr .r8 = 0 := by rw [e₃.gpr, z₂]
  have z₄ : u₄.gpr .r8 = 0 := by rw [e₄.gpr, z₃]
  have mv : v₄.mem = ((((t₈.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (s.gpr .r8 + BitVec.ofNat 64 40) (0 : BitVec 64)).writeW (s.gpr .r8 + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (s.gpr .r8 + BitVec.ofNat 64 56) (0 : BitVec 64)) := by
    rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, z₁, z₂, z₃, z₄]
  have gp : ∀ r ∈ preserved, v₄.gpr r = t₈.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, p6, -⟩ := pres_args hr
    rw [g₄.other _ p6, g₃.other _ p5, g₂.other _ p4, g₁.other _ p3, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr,
      e₁.other _ (by revert hr; cases r <;> decide)]
  have cont : ∀ d, 32 ≤ d → d + 8 ≤ 64 → Region.Contains ⟨s.gpr .r8 + BitVec.ofNat 64 32, 32⟩
      (s.gpr .r8 + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  have fv : Frame [⟨s.gpr .r8 + BitVec.ofNat 64 32, 32⟩] t₈.mem v₄.mem := by
    rw [mv]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cont 40 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cont 48 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cont 56 (by decide) (by decide))
  have rr : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i + 8 ≤ j ∨ j + 8 ≤ i → i + 8 ≤ 192 → j + 8 ≤ 192 →
      (x.writeW (s.gpr .r8 + BitVec.ofNat 64 j) v).readW (s.gpr .r8 + BitVec.ofNat 64 i) 64 =
        x.readW (s.gpr .r8 + BitVec.ofNat 64 i) 64 :=
    fun x i j v h hi hj => Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)
  have hz : ∀ k < 4, v₄.mem.readW (s.gpr .r8 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * k)) 64 = 0 := by
    intro k hk
    rw [mv, Offset.add_add]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [show 32 + 8 * 0 = 32 from rfl, rr _ 32 56 _ (by decide) (by decide) (by decide),
        rr _ 32 48 _ (by decide) (by decide) (by decide), rr _ 32 40 _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 1 = 40 from rfl, rr _ 40 56 _ (by decide) (by decide) (by decide),
        rr _ 40 48 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 2 = 48 from rfl, rr _ 48 56 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 3 = 56 from rfl, Mem.readW_writeW_self64]
  have g₃' : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → v₄.gpr r = t₈.gpr r :=
    fun r a b c d e => by
      rw [g₄.other _ d, g₃.other _ c, g₂.other _ b, g₁.other _ a, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ e]
  refine ⟨verStep hp h₈ (by rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd, e₅.rd, e₄.rd, e₃.rd, e₂.rd, e₁.rd])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr, e₁.wr])
    (by rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp, e₁.sp]) gp fv fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨32, 32, by decide, rfl⟩), ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · rw [g₄.other _ (by decide), g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), e25]
  · rw [g₄.gpr, g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), BitVec.add_zero,
      e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr, e₁.other _ (by decide), h₈.regs _ (by decide)]; rfl
  · have low : bytesAt v₄.mem (s.gpr .r8) 32 = bytesAt t₈.mem (s.gpr .r8) 32 :=
      bytes_keep fv (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide)
    rw [Proof.Ed25519.signatureBytes_split, low, hpost, bytes32_zero hz, ← Proof.Ed25519.reduced_challenge]

end VG.Proof.Ed25519.PPC64LE.Whole
