module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_public_key_expanded` on PPC64LE, with its frame as an argument

`out` in `r3`, the seed's digest (`n` bytes, 64 here) at `r4`, `scratch` in
`r5` and the frame `F` (144 bytes) in `r6`: the registers saved at `96(F)`,
the seed's digest left in `F` by the first step, its first half pruned into
`64(F)`, and `[s]B` encoded into `out` by a call of `vg_ed25519_scalar_base`
(`publicKeyWith_wp`). The first step copies the digest at `r4` (`pkCopy_ok`,
`publicKeyExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt decodeLE)
open VG.Impl.Ed25519.PPC64LE (combSym combWord)

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 144⟩, below s.sp 48]

/-- The precondition, by register, with `n` bytes at `r4`. -/
structure PkPre (n : Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, n⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 144⟩]
  oS : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r4, n⟩
  oC : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r5, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r6, 144⟩
  sC : Region.Disjoint ⟨s.gpr .r4, n⟩ ⟨s.gpr .r5, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r4, n⟩ ⟨s.gpr .r6, 144⟩
  cF : Region.Disjoint ⟨s.gpr .r5, 8192⟩ ⟨s.gpr .r6, 144⟩
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint ⟨s.gpr .r3, 32⟩
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r4, n⟩
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r5, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r6, 144⟩
  tfit : (s.syms combSym).toNat + 49152 ≤ 2 ^ 64
  words : ∀ q < 64 * 96, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q
  tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r

/-- The values in `r20`–`r23`. -/
def pkV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r5 | .r23 => s.gpr .r6 | _ => 0

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .r6) 96 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

/-- The slots are apart from everything but the frame's first 96 bytes. -/
theorem pk_slot {n : Nat} {s : State} (hp : PkPre n s) :
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r3, 32⟩ ∧
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r5, 8192⟩ ∧
    (slotArea (s.gpr .r6) 96 pkRegs).Disjoint (below s.sp 48) ∧
    ∀ d n, d + n ≤ 96 → (slotArea (s.gpr .r6) 96 pkRegs).Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .r6) 96 pkRegs) ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

/-- The setup: the registers saved, the pointers moved to `r20`–`r23`. -/
theorem pkSetup_ok {n : Nat} {s : State} (hp : PkPre n s) :
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

/-- The digest, while the body runs. -/
theorem pk_seed {n : Nat} {s t : State} (hp : PkPre n s) (h : PkInv s t) (hn : n < 2 ^ 64) :
    bytesAt t.mem (s.gpr .r4) n = bytesAt s.mem (s.gpr .r4) n :=
  bytes_keep h.frame hn fun r hr => by
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

/-- The function, from a first step that leaves the digest of `seed` at `0(F)`. -/
theorem publicKeyWith_wp (B : BaseOk) {n : Nat} {s : State} (hp : PkPre n s) {digest : Prog isa}
    {seed : List Byte}
    (hd : ∀ t, PkInv s t → WP isa digest t fun t' => PkInv s t' ∧
      bytesAt t'.mem (s.gpr .r6) 64 = Spec.Sha512.sha512 seed) :
    WP isa (publicKeyWith digest) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.lr = s.lr ∧ bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey seed := by
  obtain ⟨hsl₁, hsl₂, -, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, wO, wF, -⟩ := pk_inW (s := s)
  have hFw : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold publicKeyWith
  refine WP.seq (WP.mono_syms (pkSetup_ok hp) fun t₁ h₁ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (hd t₁ h₁) fun t₄ ⟨h₄, dg⟩ sy₄ => ?_)
  -- The pruning, and the arguments of `scalar_base`.
  have hFr : ∀ d, d + 8 ≤ 144 → InRegions (t₄.rd ++ t₄.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) hd (by omega)
  have hFw' : ∀ d, d + 8 ≤ 144 → InRegions t₄.wr (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base hFw hd (by omega)
  refine WP.seq (WP.of_syms <| prune_ok (f := .r23) (F := s.gpr .r6) (d := 0) (o := 64) (by decide) (by decide) (h₄.regs _ (by decide))
    (by decide) (by decide) (by decide) (fun k hk => hFr _ (by omega)) (fun k hk => hFw' _ (by omega))
    fun u hu hfu hpr => ?_)
  unfold mov
  refine wp_addi (by decide) (by decide) fun v₁ e₁ => wp_addi (by decide) (by decide) fun v₂ e₂ =>
    wp_addi (by decide) (by decide) fun t₅ e₃ => WP.block_nil fun sy₅ => ?_
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
      Spec.Ed25519.prune (Spec.Sha512.sha512 seed) := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  have ce : ∀ q, q ∉ linkRegs → ∀ rd wr, (t₅.callEntry.withRegions rd wr).gpr q = t₅.gpr q :=
    fun q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have sc4 : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  have sy : t₅.syms combSym = s.syms combSym := by rw [sy₅, sy₄, sy₁]
  have wd₅ : ∀ q < 64 * 96, t₅.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q :=
    fun q hq => by
      rw [← hp.words q hq]
      exact h₅.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega)) hp.tW
        (by decide)
  refine WP.seq (WP.call (k := baseRV) B (rd := [⟨s.gpr .r6 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩]) (basePre_call c3 c4 c5 sy hp.oC
      (hp.cF.symm.sub_left sc4) hp.tfit wd₅ (hp.tW _ (by simp)))
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

/-- The digest at `r4` copied to `0(F)`. -/
theorem pkCopy_ok {s t : State} (hp : PkPre 64 s) (h : PkInv s t) :
    WP isa (.block (copyIn64 .r21 .r23 0)) t fun t' => PkInv s t' ∧
      bytesAt t'.mem (s.gpr .r6) 64 = bytesAt s.mem (s.gpr .r4) 64 := by
  obtain ⟨-, -, -, hsl₄⟩ := pk_slot hp
  obtain ⟨-, -, wF, -⟩ := pk_inW (s := s)
  have hS : (⟨s.gpr .r4, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  have hFw : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have F0 : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 0, 64⟩ ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  rw [← List.append_nil (copyIn64 .r21 .r23 0)]
  refine copy64_ok (A := s.gpr .r4) (B := s.gpr .r6) (o := 0) (by decide) (by decide) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide) (by decide)
    (fun k hk => by rw [h.rd, h.wr]; exact in_base (List.mem_append_left _ hS) (by omega) (by omega))
    (fun k hk => by rw [h.wr]; exact in_base hFw (by omega) (by omega))
    (hp.sF.sub_right F0) fun u hu hfu hb => WP.block_nil ⟨h.step pkRegs_pres hu.rd hu.wr hu.sp
      (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, wF, F0⟩)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 0 64 (by decide)), ?_⟩
  rw [← BitVec.add_zero (s.gpr .r6), hb, pk_seed hp h (by decide)]

/-- `vg_ed25519_public_key_expanded`: the public key of every seed whose digest is at `r4`. -/
theorem publicKeyExpanded_wp (B : BaseOk) {s : State} (hp : PkPre 64 s) {seed : List Byte}
    (hs : bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed) :
    WP isa publicKeyExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey seed :=
  publicKeyWith_wp B hp fun _ h => WP.mono (pkCopy_ok hp h) fun _ ⟨h', e⟩ => ⟨h', e.trans hs⟩

end VG.Proof.Ed25519.PPC64LE.Whole
