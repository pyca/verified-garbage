module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_public_key` on RISCV64, with its frame as an argument

`out` in `a0`, `seed` in `a1`, `scratch` in `a2` and the frame `F` (144
bytes) in `a3`: the registers saved at `96(F)`, the seed hashed into `F`, its
first half pruned into `64(F)`, and `[s]B` encoded into `out` by a call of
`vg_ed25519_scalar_base` (`publicKey_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64 (combSym combWord)
open VG.Spec.Ed25519 (bytesAt decodeLE)

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩, below s.sp 208]

/-- The precondition, by register. -/
structure PkPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 32⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩]
  oS : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a1, 32⟩
  oC : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a2, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a3, 144⟩
  sC : Region.Disjoint ⟨s.gpr .a1, 32⟩ ⟨s.gpr .a2, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, 32⟩ ⟨s.gpr .a3, 144⟩
  cF : Region.Disjoint ⟨s.gpr .a2, 8192⟩ ⟨s.gpr .a3, 144⟩
  alC : (s.gpr .a2).toNat % 8 = 0
  alF : (s.gpr .a3).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bO : (below s.sp 208).Disjoint ⟨s.gpr .a0, 32⟩
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a1, 32⟩
  bC : (below s.sp 208).Disjoint ⟨s.gpr .a2, 8192⟩
  bF : (below s.sp 208).Disjoint ⟨s.gpr .a3, 144⟩
  tal : (s.syms combSym).toNat % 8 = 0
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `s7`–`s10`. -/
def pkV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a0 | .s8 => s.gpr .a1 | .s9 => s.gpr .a2 | .s10 => s.gpr .a3 | _ => 0

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .a3) 96 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 96 bytes. -/
theorem pk_slot {s : State} (hp : PkPre s) :
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a0, 32⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a2, 8192⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint (below s.sp 208) ∧
    ∀ d n, d + n ≤ 96 → (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a3 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .a3) 96 pkRegs) ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

/-- The setup: the registers saved, the pointers moved to `s7`–`s10`. -/
theorem pkSetup_ok {s : State} (hp : PkPre s) :
    WP isa (.block (saveRegs .a3 96 pkRegs ++
      [mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, mov .s10 .a3])) s (PkInv s) := by
  have hF : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsl : ∀ p ∈ slots 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega)) fun u hu hsv hfr => ?_
  unfold mov
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => WP.block_nil ?_
  have m : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → u₄.gpr r = u.gpr r := fun r a b c d => by
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  have gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  refine ⟨by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd], by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr],
    by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp], fun r hr => ?_, fun r hr hn => ?_, m ▸ hsv,
    m ▸ (hfr.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨⟨s.gpr .a3, 144⟩, by simp, Offset.sub_base _ (by decide)⟩)⟩
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, gu]; rfl
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), gu]; rfl
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
    · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), gu]; rfl
  · simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨a, b, c, d⟩ := hn
    rw [g r a b c d, gu r]

theorem pkV_s7 (s : State) : pkV s .s7 = s.gpr .a0 := rfl
theorem pkV_s8 (s : State) : pkV s .s8 = s.gpr .a1 := rfl
theorem pkV_s9 (s : State) : pkV s .s9 = s.gpr .a2 := rfl
theorem pkV_s10 (s : State) : pkV s .s10 = s.gpr .a3 := rfl

/-- The seed, while the body runs. -/
theorem pk_seed {s t : State} (hp : PkPre s) (h : PkInv s t) :
    bytesAt t.mem (s.gpr .a1) 32 = bytesAt s.mem (s.gpr .a1) 32 :=
  bytes_keep h.frame (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oS.symm
    · exact hp.sC
    · exact hp.sF
    · exact hp.bS.symm

/-- Region facts for `Inv.step`. -/
theorem pk_inW {s : State} : (⟨s.gpr .a2, 8192⟩ : Region) ∈ pkW s ∧ (⟨s.gpr .a0, 32⟩ : Region) ∈ pkW s ∧
    (⟨s.gpr .a3, 144⟩ : Region) ∈ pkW s ∧ below s.sp 208 ∈ pkW s := by simp

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem publicKey_wp (C : ShaOK) {s : State} (hp : PkPre s) :
    WP isa publicKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .a1) 32) := by
  obtain ⟨hsl₁, hsl₂, hsl₃, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, wO, wF, wB⟩ := pk_inW (s := s)
  have hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have env : ∀ t, PkInv s t → ScEnv (s.gpr .a2) t := fun t h =>
    ⟨by rw [h.wr]; exact hCw, by rw [h.sp]; exact hp.spal, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩
  -- Steps that write the scratch space and the callees' frames.
  have scStep : ∀ {t t'}, PkInv s t → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) → Frame [⟨s.gpr .a2, 8192⟩, below t.sp 208] t.mem t'.mem →
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
  refine WP.seq (WP.mono_syms (pkSetup_ok hp) fun t₁ h₁ sy₁ => ?_)
  -- `init`.
  refine WP.seq (WP.of_syms <| hashInit_ok C (sr := .s9) (h₁.regs _ (by decide)) (env t₁ h₁)
    fun t₂ a b c f g hr₂ sy₂ => ?_)
  have h₂ : PkInv s t₂ := scStep h₁ a b c g f
  -- `update` with the seed.
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .s9) (src := .s8) (off := 0) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (env t₂ h₂)
    (fun a n hi => by obtain ⟨r, hr, hc⟩ := hi; rw [h₂.rd, hp.rd]
                      exact ⟨r, List.mem_append_left _ (by simp at hr; simp [hr]), hc⟩)
    hp.sC (by rw [h₂.sp]; exact hp.bS) fun t₃ a b c f g hr₃ sy₃ => ?_)
  have h₃ : PkInv s t₃ := scStep h₂ a b c g f
  have r₃ : Repr t₃.mem (s.gpr .a2) (bytesAt s.mem (s.gpr .a1) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, pk_seed hp h₂] at this
  -- `finalize` into `F`.
  refine WP.seq (WP.of_syms <| hashFinalize_ok C (sr := .s9) (f := .s10) (o := 0) (out := s.gpr .a3) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (fun _ _ _ => rfl) (env t₃ h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₃.wr]; exact ⟨_, hFw, 0, by simp, by simp⟩)
    (hp.cF.symm.sub_left (Region.sub_prefix (by decide)))
    (by rw [h₃.sp]; exact hp.bF.sub_right (Region.sub_prefix (by decide))) fun t₄ a b c f g hd₄ sy₄ => ?_)
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
  have dg : bytesAt t₄.mem (s.gpr .a3) 64 = Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a1) 32) :=
    hd₄ _ r₃ (by simp [bytesAt]) (by simp [bytesAt])
  -- The pruning, and the arguments of `scalar_base`.
  have hFr : ∀ d, d + 8 ≤ 144 → InRegions (t₄.rd ++ t₄.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) hd (by omega)
  have hFw' : ∀ d, d + 8 ≤ 144 → InRegions t₄.wr (s.gpr .a3 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base hFw hd (by omega)
  refine WP.seq (WP.of_syms <| prune_ok (f := .s10) (F := s.gpr .a3) (d := 0) (o := 64) (by decide) (h₄.regs _ (by decide)) hp.alF
    (by decide) (by decide) (by decide) (fun k hk => hFr _ (by omega)) (fun k hk => hFw' _ (by omega))
    fun u hu hfu hpr => ?_)
  unfold mov
  refine wp_mv fun v₁ e₁ => wp_addi (by decide) fun v₂ e₂ =>
    wp_mv fun t₅ e₃ => WP.block_nil fun sy₅ => ?_
  have g₅ : ∀ r ∈ preserved, t₅.gpr r = t₄.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, -, -⟩ := pres_args hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, hu.gpr _ (by revert hr; cases r <;> decide)]
  have m₅ : t₅.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  have h₅ : PkInv s t₅ := h₄.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, hu.rd])
    (by rw [e₃.wr, e₂.wr, e₁.wr, hu.wr]) (by rw [e₃.sp, e₂.sp, e₁.sp, hu.sp]) g₅ (m₅ ▸ hfu)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, wF, Offset.sub_base _ (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 64 32 (by decide)
  have c3 : t₅.gpr .a0 = s.gpr .a0 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  have c4 : t₅.gpr .a1 = s.gpr .a3 + BitVec.ofNat 64 64 := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hu.gpr _ (by decide), h₄.regs _ (by decide)]; rfl
  have c5 : t₅.gpr .a2 = s.gpr .a2 := by
    rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  have hdec : decodeLE (bytesAt t₅.mem (s.gpr .a3 + BitVec.ofNat 64 64) 32) =
      Spec.Ed25519.prune (Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a1) 32)) := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  have ce : ∀ q, q ∉ linkRegs → ∀ rd wr, (t₅.callEntry.withRegions rd wr).gpr q = t₅.gpr q :=
    fun q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have sc4 : Region.Sub ⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  have sy : t₅.syms combSym = s.syms combSym := by rw [sy₅, sy₄, sy₃, sy₂, sy₁]
  have wd₅ : ∀ q < 64 * 96, t₅.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q :=
    fun q hq => by
      rw [← hp.words q hq]
      exact h₅.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega)) hp.tW
        (by decide)
  refine WP.seq (WP.call (k := baseRV) base_ok' (rd := [⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩]) (basePre_call c3 c4 c5 sy hp.alC hp.oC
      (hp.cF.symm.sub_left sc4) hp.tal hp.tfit wd₅ (hp.tW _ (by simp)))
    (Covers.of_sub fun r hr => by
      rw [h₅.rd, h₅.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 144 by decide⟩
      · exact ⟨TBL (s.syms combSym), List.mem_append_left _ (by rw [hp.rd]; simp), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hOw, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₅.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw, hc⟩
      · exact ⟨_, hCw, hc⟩) (fun t₆ a b c hf hg _ hpost => ?_) (by decide +kernel))
  simp only [baseRV, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
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
  refine restore_ok h₆ hp.alF (h₆.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₆.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega))
    fun t₇ g₇ sp₇ ra₇ m₇ _ => ⟨g₇, sp₇, ra₇, ?_⟩
  rw [m₇, hpost, Spec.Ed25519.scalarBase, hdec]
  rfl

end VG.Proof.Ed25519.RISCV64.Whole
