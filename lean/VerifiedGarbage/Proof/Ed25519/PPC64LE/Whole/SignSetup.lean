module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed25519_sign_cached` on PPC64LE: the setup

`out` in `r3`, `seed` in `r4`, `pk` in `r5`, the message in `r6` (`len` in
`r7`), `scratch` in `r8` and the frame `F` (288 bytes) in `r9`. The setup
saves the registers at `224(F)`, moves what lives across calls to `r20`–`r25`
and copies `pk` to `192(F)` (`signSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

/-- The message. -/
abbrev msgR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩

/-- The precondition, by register. -/
structure SignPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩, ⟨s.gpr .r5, 32⟩, msgR s]
  wr : s.wr = [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 288⟩]
  oS : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r4, 32⟩
  oP : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r5, 32⟩
  oM : Region.Disjoint ⟨s.gpr .r3, 64⟩ (msgR s)
  oC : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r8, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .r3, 64⟩ ⟨s.gpr .r9, 288⟩
  sC : Region.Disjoint ⟨s.gpr .r4, 32⟩ ⟨s.gpr .r8, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r4, 32⟩ ⟨s.gpr .r9, 288⟩
  pC : Region.Disjoint ⟨s.gpr .r5, 32⟩ ⟨s.gpr .r8, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .r5, 32⟩ ⟨s.gpr .r9, 288⟩
  mC : Region.Disjoint (msgR s) ⟨s.gpr .r8, 8192⟩
  mF : Region.Disjoint (msgR s) ⟨s.gpr .r9, 288⟩
  cF : Region.Disjoint ⟨s.gpr .r8, 8192⟩ ⟨s.gpr .r9, 288⟩
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint ⟨s.gpr .r3, 64⟩
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r4, 32⟩
  bP : (below s.sp 48).Disjoint ⟨s.gpr .r5, 32⟩
  bM : (below s.sp 48).Disjoint (msgR s)
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r8, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r9, 288⟩
  pk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32)

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 288⟩, below s.sp 48]

/-- The values in `r20`–`r25`. -/
def signV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r6 | .r23 => s.gpr .r7 | .r24 => s.gpr .r8
  | .r25 => s.gpr .r9 | _ => 0

abbrev SignInv (s : State) : State → Prop := Inv s (s.gpr .r9) 224 signRegs (signV s) (signW s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 224 bytes. -/
theorem sign_slot {s : State} (hp : SignPre s) :
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r3, 64⟩ ∧
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (slotArea (s.gpr .r9) 224 signRegs).Disjoint (below s.sp 48) ∧
    ∀ d n, d + n ≤ 224 → (slotArea (s.gpr .r9) 224 signRegs).Disjoint ⟨s.gpr .r9 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .r9) 224 signRegs) ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

theorem signV_r20 (s : State) : signV s .r20 = s.gpr .r3 := rfl
theorem signV_r21 (s : State) : signV s .r21 = s.gpr .r4 := rfl
theorem signV_r22 (s : State) : signV s .r22 = s.gpr .r6 := rfl
theorem signV_r23 (s : State) : signV s .r23 = s.gpr .r7 := rfl
theorem signV_r24 (s : State) : signV s .r24 = s.gpr .r8 := rfl
theorem signV_r25 (s : State) : signV s .r25 = s.gpr .r9 := rfl

/-- The setup: the registers saved, the pointers moved to `r20`–`r25`, `pk` copied to `192(F)`. -/
theorem signSetup_ok {s : State} (hp : SignPre s) :
    WP isa (.block signSetup) s fun t => SignInv s t ∧
      bytesAt t.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .r5) 32 := by
  have hF : (⟨s.gpr .r9, 288⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 224 signRegs, p.2 + 8 ≤ 288 := by decide
  obtain ⟨-, -, -, hsl₄⟩ := sign_slot hp
  unfold signSetup
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu _ hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ =>
    wp_addi (by decide) (by decide) fun u₅ h₅ => wp_addi (by decide) (by decide) fun u₆ h₆ => ?_
  have m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g₆ : ∀ r, r ∉ signRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  have gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
  have rd₆ : u₆.rd = s.rd := by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  have wr₆ : u₆.wr = s.wr := by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  have sp₆ : u₆.sp = s.sp := by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  have e5 : u₆.gpr .r5 = s.gpr .r5 := by rw [g₆ _ (by decide), gu _ (by decide)]
  have e25 : u₆.gpr .r25 = s.gpr .r9 := by
    rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), BitVec.add_zero, gu _ (by decide)]
  have hP : (⟨s.gpr .r5, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have hsep : ∀ i < 4, ∀ j < 4, Mem.Sep (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
      (s.gpr .r9 + BitVec.ofNat 64 (192 + 8 * j)) 8 := fun i hi j hj =>
    hp.pF.sep (Offset.contains_base _ (by omega) (by omega)) (Offset.contains_base _ (by omega) (by omega))
  rw [← List.append_nil (copyIn .r5 .r25 192)]
  refine copy_ok (A := s.gpr .r5) (B := s.gpr .r9) (da := fun k => 8 * k) (db := fun k => 192 + 8 * k)
    (R := ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩) (by decide) (by decide) (by decide) (by decide) e5 e25
    (fun k hk => ⟨by omega, by omega⟩) (fun k hk => ⟨by omega, by omega⟩)
    (fun k hk => by rw [rd₆, wr₆]; exact in_base (List.mem_append_left _ hP) (by omega) (by omega))
    (fun k hk => by rw [wr₆]; exact in_base hF (by omega) (by omega))
    (fun k hk => Offset.contains _ (by omega) (by omega) (by omega)) hsep
    (fun i hi j hj hij => Offset.sep _ (by omega) (by omega) (by omega)) fun t ht hft hw => WP.block_nil ?_
  have fin : Frame [slotArea (s.gpr .r9) 224 signRegs, ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩] s.mem t.mem :=
    (hfr.mono (by simp)).trans (by rw [m₆] at hft; exact hft.mono (by simp))
  refine ⟨⟨by rw [ht.rd, rd₆], by rw [ht.wr, wr₆], by rw [ht.sp, sp₆], fun r hr => ?_, fun r hr hn => ?_, ?_,
    fin.sub fun r hr => ?_⟩, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert)]
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    · rw [e25]; rfl
  · have h8 : r ∉ [Reg.r8] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h8, g₆ r hn, gu r fun e => r0_pres (e ▸ hr)]
  · refine (hsv.frame_in (slots_in 224 signRegs) (m₆ ▸ hft) fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
  · refine bytes32_of_words fun k hk => ?_
    have hw' := hw k hk
    have hr' : u.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * k)) 64 = s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * k)) 64 :=
      hfr.readW (r := ⟨s.gpr .r5, 32⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.pF.sub_right (Offset.sub_base _ (by decide)))) (by decide)
    rw [Offset.add_add, hw', m₆, hr']

/-- The regions a step of the body may write: the scratch space, the callees' frames, `out`, its
halves, or the frame below the slots. -/
def SignWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .r8, 8192⟩ ∨ r = below s.sp 48 ∨ r = ⟨s.gpr .r3, 64⟩ ∨ r = ⟨s.gpr .r3 + BitVec.ofNat 64 32, 32⟩ ∨
    r = ⟨s.gpr .r3, 32⟩ ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .r9 + BitVec.ofNat 64 d, n⟩

theorem signStep {s t t' : State} (hp : SignPre s) (h : SignInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, SignWr s r) : SignInv s t' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := sign_slot hp
  refine Inv.step h signRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .r3, 64⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .r3, 64⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s.gpr .r9, 288⟩, by simp, Offset.sub_base _ (by omega)⟩
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact h₂
    · exact h₃
    · exact h₁
    · exact h₁.sub_right (Offset.sub_base _ (by decide))
    · exact h₁.sub_right (Region.sub_prefix (by decide))
    · exact h₄ d n hdn

end VG.Proof.Ed25519.PPC64LE.Whole
