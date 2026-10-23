module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_public_key` on PPC64LE, with its frame as an argument

`out` in `r3`, `seed` in `r4`, `scratch` in `r5` and the frame `F` (144
bytes) in `r6`: the registers saved at `96(F)`, the seed hashed into `F`, its
first half pruned into `64(F)`, and `[s]B` encoded into `out` by a call of
`vg_ed25519_scalar_base` (`publicKey_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt decodeLE)

/-- The precondition, by register. -/
structure PkPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 144⟩]
  oS : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r4, 32⟩
  oC : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r5, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r6, 144⟩
  sC : Region.Disjoint ⟨s.gpr .r4, 32⟩ ⟨s.gpr .r5, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r4, 32⟩ ⟨s.gpr .r6, 144⟩
  cF : Region.Disjoint ⟨s.gpr .r5, 8192⟩ ⟨s.gpr .r6, 144⟩
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint ⟨s.gpr .r3, 32⟩
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r4, 32⟩
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r5, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r6, 144⟩

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 144⟩, below s.sp 48]

/-- The values in `r20`–`r23`. -/
def pkV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r5 | .r23 => s.gpr .r6 | _ => 0

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .r6) 96 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 96 bytes. -/
theorem pk_slot {s : State} (hp : PkPre s) :
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r3, 32⟩ ∧
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r5, 8192⟩ ∧
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint (below s.sp 48) ∧
    ∀ d n, d + n ≤ 96 → (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .r6) 96 pkRegs) ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

/-- The setup: the registers saved, the pointers moved to `r20`–`r23`. -/
theorem pkSetup_ok {s : State} (hp : PkPre s) :
    WP isa (.block (saveRegs .r6 96 pkRegs ++
      [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6])) s (PkInv s) := by
  have hF : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu _ hsv hfr => ?_
  unfold mov
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ => WP.block_nil ?_
  have m : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g : ∀ r, r ≠ .r20 → r ≠ .r21 → r ≠ .r22 → r ≠ .r23 → u₄.gpr r = u.gpr r := fun r a b c d => by
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  have gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
  refine ⟨by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd], by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr],
    by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp], fun r hr => ?_, fun r hr hn => ?_, m ▸ hsv,
    m ▸ (hfr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨⟨s.gpr .r6, 144⟩, by simp, Offset.sub_base _ (by decide)⟩)⟩
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, BitVec.add_zero,
        gu _ (by decide)]; rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), BitVec.add_zero,
        gu _ (by decide)]; rfl
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero,
        gu _ (by decide)]; rfl
    · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), BitVec.add_zero,
        gu _ (by decide)]; rfl
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨a, b, c, d⟩ := hn
    rw [g r a b c d, gu r fun e => r0_pres (e ▸ hr)]

theorem pkV_r20 (s : State) : pkV s .r20 = s.gpr .r3 := rfl
theorem pkV_r21 (s : State) : pkV s .r21 = s.gpr .r4 := rfl
theorem pkV_r22 (s : State) : pkV s .r22 = s.gpr .r5 := rfl
theorem pkV_r23 (s : State) : pkV s .r23 = s.gpr .r6 := rfl

/-- The seed, while the body runs. -/
theorem pk_seed {s t : State} (hp : PkPre s) (h : PkInv s t) :
    bytesAt t.mem (s.gpr .r4) 32 = bytesAt s.mem (s.gpr .r4) 32 :=
  bytes_keep h.frame (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oS.symm
    · exact hp.sC
    · exact hp.sF
    · exact hp.bS.symm

/-- Region facts for `Inv.step`. -/
theorem pk_inW {s : State} : (⟨s.gpr .r5, 8192⟩ : Region) ∈ pkW s ∧ (⟨s.gpr .r3, 32⟩ : Region) ∈ pkW s ∧
    (⟨s.gpr .r6, 144⟩ : Region) ∈ pkW s ∧ below s.sp 48 ∈ pkW s := by simp

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem publicKey_wp (C : ShaOK) {s : State} (hp : PkPre s) :
    WP isa publicKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32) := by
  obtain ⟨hsl₁, hsl₂, hsl₃, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, wO, wF, wB⟩ := pk_inW (s := s)
  have hFw : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have env : ∀ t, PkInv s t → ScEnv (s.gpr .r5) t := fun t h =>
    ⟨by rw [h.wr]; exact hCw, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩
  -- Steps that write the scratch space and the callees' frames.
  have scStep : ∀ {t t'}, PkInv s t → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) → Frame [⟨s.gpr .r5, 8192⟩, below t.sp 48] t.mem t'.mem →
      PkInv s t' := fun h a b c d e => h.step pkRegs_pres a b c d e (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, wC, sub_refl _⟩
        · exact ⟨_, by rw [h.sp]; exact wB, sub_refl _⟩) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hsl₂
        · rw [h.sp]; exact hsl₃
  unfold publicKey
  refine WP.seq (WP.mono (pkSetup_ok hp) fun t₁ h₁ => ?_)
  -- `init`.
  refine WP.seq (hashInit_ok C (sr := .r22) (by decide) (h₁.regs _ (by decide)) (env t₁ h₁)
    fun t₂ a b c f g hr₂ => ?_)
  have h₂ : PkInv s t₂ := scStep h₁ a b c g f
  -- `update` with the seed.
  refine WP.seq (hashUpdate_ok C (sr := .r22) (src := .r21) (off := 0) (len := 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 0) (by decide)) (Sets.li (d := .r6) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (env t₂ h₂)
    (fun a n hi => by obtain ⟨r, hr, hc⟩ := hi; rw [h₂.rd, hp.rd]
                      exact ⟨r, List.mem_append_left _ (by simpa using hr), hc⟩)
    hp.sC (by rw [h₂.sp]; exact hp.bS) fun t₃ a b c f g hr₃ => ?_)
  have h₃ : PkInv s t₃ := scStep h₂ a b c g f
  have r₃ : Repr t₃.mem (s.gpr .r5) (bytesAt s.mem (s.gpr .r4) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, pk_seed hp h₂] at this
  -- `finalize` into `F`.
  refine WP.seq (hashFinalize_ok C (sr := .r22) (f := .r23) (o := 0) (out := s.gpr .r6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .r4) (k := 32) (by decide)) (fun _ _ _ => rfl) (env t₃ h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₃.wr]; exact ⟨_, hFw, 0, by simp, by simp⟩)
    (hp.cF.symm.sub_left (Region.sub_prefix (by decide)))
    (by rw [h₃.sp]; exact hp.bF.sub_right (Region.sub_prefix (by decide))) fun t₄ a b c f g hd₄ => ?_)
  have h₄ : PkInv s t₄ := h₃.step pkRegs_pres a b c g f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, wC, sub_refl _⟩
      · exact ⟨_, wF, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by rw [h₃.sp]; exact wB, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hsl₂
      · simpa using hsl₄ 0 64 (by decide)
      · rw [h₃.sp]; exact hsl₃
  have dg : bytesAt t₄.mem (s.gpr .r6) 64 = Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .r4) 32) :=
    hd₄ _ r₃ (by simp [bytesAt]) (by simp [bytesAt])
  -- The pruning, and the arguments of `scalar_base`.
  have hFr : ∀ d, d + 8 ≤ 144 → InRegions (t₄.rd ++ t₄.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) hd (by omega)
  have hFw' : ∀ d, d + 8 ≤ 144 → InRegions t₄.wr (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base hFw hd (by omega)
  refine WP.seq (prune_ok (f := .r23) (F := s.gpr .r6) (d := 0) (o := 64) (by decide) (by decide) (h₄.regs _ (by decide))
    (by decide) (by decide) (by decide) (fun k hk => hFr _ (by omega)) (fun k hk => hFw' _ (by omega))
    fun u hu hfu hpr => ?_)
  unfold mov
  refine wp_addi (by decide) (by decide) fun v₁ e₁ => wp_addi (by decide) (by decide) fun v₂ e₂ =>
    wp_addi (by decide) (by decide) fun t₅ e₃ => WP.block_nil ?_
  have g₅ : ∀ r ∈ preserved, t₅.gpr r = t₄.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, -, -⟩ := pres_args hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, hu.gpr _ (by revert hr; cases r <;> decide)]
  have m₅ : t₅.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  have h₅ : PkInv s t₅ := h₄.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, hu.rd])
    (by rw [e₃.wr, e₂.wr, e₁.wr, hu.wr]) (by rw [e₃.sp, e₂.sp, e₁.sp, hu.sp]) g₅ (m₅ ▸ hfu)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, wF, Offset.sub_base _ (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 64 32 (by decide)
  have c3 : t₅.gpr .r3 = s.gpr .r3 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, BitVec.add_zero, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  have c4 : t₅.gpr .r4 = s.gpr .r6 + BitVec.ofNat 64 64 := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hu.gpr _ (by decide), h₄.regs _ (by decide)]; rfl
  have c5 : t₅.gpr .r5 = s.gpr .r5 := by
    rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), BitVec.add_zero, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  have hdec : decodeLE (bytesAt t₅.mem (s.gpr .r6 + BitVec.ofNat 64 64) 32) =
      Spec.Ed25519.prune (Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .r4) 32)) := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  have ce : ∀ q, q ∉ linkRegs → ∀ rd wr, (t₅.callEntry.withRegions rd wr).gpr q = t₅.gpr q :=
    fun q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have sc4 : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  refine WP.seq (WP.call (k := basePPC) base_ok' (rd := [⟨s.gpr .r6 + BitVec.ofNat 64 64, 32⟩])
    (wr := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩]) ⟨by rw [State.withRegions_rd, ce _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ (by decide), ce _ (by decide), c3, c5],
      by rw [ce _ (by decide), ce _ (by decide), c3, c5]; exact hp.oC,
      by rw [ce _ (by decide), ce _ (by decide), c4, c5]; exact hp.cF.symm.sub_left sc4⟩
    (Covers.of_sub fun r hr => by
      rw [h₅.rd, h₅.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 144 by decide⟩
      · exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₅.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw, hc⟩
      · exact ⟨_, hCw, hc⟩) (fun t₆ a b c hf hg _ hpost => ?_) (by decide +kernel))
  simp only [basePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    c3, c4] at hpost
  have h₆ : PkInv s t₆ := h₅.step pkRegs_pres a b c hg hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, wO, sub_refl _⟩
      · exact ⟨_, wC, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hsl₁
      · exact hsl₂
  -- The restores.
  have hrl : ∀ p ∈ restoreList 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine restore_ok h₆ (by decide) (h₆.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₆.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega))
    fun t₇ g₇ sp₇ lr₇ m₇ _ => ⟨g₇, sp₇, lr₇, ?_⟩
  rw [m₇, hpost, Spec.Ed25519.scalarBase, hdec]
  rfl

end VG.Proof.Ed25519.PPC64LE.Whole
