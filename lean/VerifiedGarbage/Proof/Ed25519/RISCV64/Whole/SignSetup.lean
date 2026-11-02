module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_sign_cached` on RISC-V: the setup

`out` in `a0`, `seed` in `a1`, `pk` in `a2`, the message in `a3` (`len` in
`a4`), `scratch` in `a5` and the frame `F` (288 bytes) in `a6`. The setup
saves the registers at `224(F)`, moves what lives across calls to `s7`–`s11`
and `seed` to `s1`, and copies `pk` to `192(F)` (`signSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combWord)

/-- The message. -/
abbrev msgR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [⟨s.gpr .a0, 64⟩, ⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 288⟩, below s.sp 208]

/-- The precondition, by register. -/
structure SignPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 32⟩, ⟨s.gpr .a2, 32⟩, msgR s, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .a0, 64⟩, ⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6, 288⟩]
  alC : (s.gpr .a5).toNat % 8 = 0
  alF : (s.gpr .a6).toNat % 8 = 0
  oS : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a1, 32⟩
  oP : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a2, 32⟩
  oM : Region.Disjoint ⟨s.gpr .a0, 64⟩ (msgR s)
  oC : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a5, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 64⟩ ⟨s.gpr .a6, 288⟩
  sC : Region.Disjoint ⟨s.gpr .a1, 32⟩ ⟨s.gpr .a5, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, 32⟩ ⟨s.gpr .a6, 288⟩
  pC : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a5, 8192⟩
  pF : Region.Disjoint ⟨s.gpr .a2, 32⟩ ⟨s.gpr .a6, 288⟩
  mC : Region.Disjoint (msgR s) ⟨s.gpr .a5, 8192⟩
  mF : Region.Disjoint (msgR s) ⟨s.gpr .a6, 288⟩
  cF : Region.Disjoint ⟨s.gpr .a5, 8192⟩ ⟨s.gpr .a6, 288⟩
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bO : (below s.sp 208).Disjoint ⟨s.gpr .a0, 64⟩
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a1, 32⟩
  bP : (below s.sp 208).Disjoint ⟨s.gpr .a2, 32⟩
  bM : (below s.sp 208).Disjoint (msgR s)
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a5, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a6, 288⟩
  pk : bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .a1) 32)
  tal : (s.syms combSym).toNat % 8 = 0
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `s1` and `s7`–`s11`. -/
def signV (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a1 | .s7 => s.gpr .a0 | .s8 => s.gpr .a3 | .s9 => s.gpr .a4 | .s10 => s.gpr .a5
  | .s11 => s.gpr .a6 | _ => 0

abbrev SignInv (s : State) : State → Prop := Inv s (s.gpr .a6) 224 signRegs (signV s) (signW s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 224 bytes. -/
theorem sign_slot {s : State} (hp : SignPre s) :
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a0, 64⟩ ∧
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a5, 8192⟩ ∧
    (slotArea (s.gpr .a6) 224 signRegs).Disjoint (below s.sp 208) ∧
    ∀ d n, d + n ≤ 224 → (slotArea (s.gpr .a6) 224 signRegs).Disjoint ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .a6) 224 signRegs) ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

theorem signV_s1 (s : State) : signV s .s1 = s.gpr .a1 := rfl
theorem signV_s7 (s : State) : signV s .s7 = s.gpr .a0 := rfl
theorem signV_s8 (s : State) : signV s .s8 = s.gpr .a3 := rfl
theorem signV_s9 (s : State) : signV s .s9 = s.gpr .a4 := rfl
theorem signV_s10 (s : State) : signV s .s10 = s.gpr .a5 := rfl
theorem signV_s11 (s : State) : signV s .s11 = s.gpr .a6 := rfl

/-- The setup: the registers saved, the pointers moved, `pk` copied to `192(F)`. -/
theorem signSetup_ok {s : State} (hp : SignPre s) :
    WP isa (.block signSetup) s fun t => SignInv s t ∧
      bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a2) 32 := by
  have hF : (⟨s.gpr .a6, 288⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 224 signRegs, p.2 + 8 ≤ 288 := by decide
  unfold signSetup
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ =>
    wp_mv fun u₅ h₅ => wp_mv fun u₆ h₆ => ?_
  have m₆ : u₆.mem = u.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g₆ : ∀ r, r ∉ signRegs → u₆.gpr r = u.gpr r := fun r hr => by
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f⟩ := hr
    rw [h₆.other _ f, h₅.other _ e, h₄.other _ d, h₃.other _ c, h₂.other _ a, h₁.other _ b]
  have gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  have rd₆ : u₆.rd = s.rd := by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  have wr₆ : u₆.wr = s.wr := by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  have sp₆ : u₆.sp = s.sp := by rw [h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  have e2 : u₆.gpr .a2 = s.gpr .a2 := by rw [g₆ _ (by decide), gu]
  have e11 : u₆.gpr .s11 = s.gpr .a6 := by rw [h₆.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]
  have hP : (⟨s.gpr .a2, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  rw [← List.append_nil (copyIn .a2 .s11 192)]
  refine copyIn_ok (P := s.gpr .a2) (F := s.gpr .a6) (o := 192) (by decide) (by decide) e2 e11 (by decide)
    (fun i hi => by rw [rd₆, wr₆]; exact in_base (List.mem_append_left _ hP) (by omega) (by omega))
    (fun i hi => by rw [wr₆]; exact in_base hF (by omega) (by omega))
    (hp.pF.sub_right (Offset.sub_base _ (by decide))) fun t ht hft hb => WP.block_nil ?_
  have fin : Frame [slotArea (s.gpr .a6) 224 signRegs, ⟨s.gpr .a6 + BitVec.ofNat 64 192, 32⟩] s.mem t.mem :=
    (hfr.mono (by simp)).trans (by rw [m₆] at hft; exact hft.mono (by simp))
  refine ⟨⟨by rw [ht.rd, rd₆], by rw [ht.wr, wr₆], by rw [ht.sp, sp₆], fun r hr => ?_, fun r hr hn => ?_, ?_,
    fin.sub fun r hr => ?_⟩, ?_⟩
  · rw [ht.gpr r (by revert hr; decide +revert)]
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
        h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₆.other _ (by decide), h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [e11]; rfl
  · have h5 : r ∉ [Reg.a5] := by
      simp only [List.mem_singleton]; intro e; rw [e] at hr; exact absurd hr (by decide)
    rw [ht.gpr r h5, g₆ r hn, gu r]
  · refine (hsv.frame_in (slots_in 224 signRegs) (m₆ ▸ hft) fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by decide)⟩
  · rw [hb]
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [m₆]
    exact hfr _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => (hp.pF.sub_right (Offset.sub_base _ (by decide))) _
        (Offset.contains_base _ (by omega) (by omega)) hc

/-- The regions a step of the body may write: the scratch space, the callees' frames, `out`, its
halves, or the frame below the slots. -/
def SignWr (s : State) (r : Region) : Prop :=
  r = ⟨s.gpr .a5, 8192⟩ ∨ r = below s.sp 208 ∨ r = ⟨s.gpr .a0, 64⟩ ∨ r = ⟨s.gpr .a0 + BitVec.ofNat 64 32, 32⟩ ∨
    r = ⟨s.gpr .a0, 32⟩ ∨ ∃ d n, d + n ≤ 224 ∧ r = ⟨s.gpr .a6 + BitVec.ofNat 64 d, n⟩

theorem signStep {s t t' : State} (hp : SignPre s) (h : SignInv s t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {Wc : List Region}
    (hf : Frame Wc t.mem t'.mem) (hW : ∀ r ∈ Wc, SignWr s r) : SignInv s t' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := sign_slot hp
  refine Inv.step h signRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a0, 64⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨s.gpr .a0, 64⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s.gpr .a6, 288⟩, by simp, Offset.sub_base _ (by omega)⟩
  · rcases hW r hr with rfl | rfl | rfl | rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact h₂
    · exact h₃
    · exact h₁
    · exact h₁.sub_right (Offset.sub_base _ (by decide))
    · exact h₁.sub_right (Region.sub_prefix (by decide))
    · exact h₄ d n hdn

end VG.Proof.Ed25519.RISCV64.Whole
