module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Expanded
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Prune
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ed25519.PPC64LE.Whole.PublicKey`, which only this module used -/

section

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
  obtain hs : Region.Sub (slotArea (s.gpr .r6) 96 pkRegs) ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega_using [h])

/-- The setup: the registers saved, the pointers moved to `r20`–`r23`. -/
theorem pkSetup_ok {n : Nat} {s : State} (hp : PkPre n s) :
    WP isa (.block (saveRegs .r6 96 pkRegs ++
      [mov .r20 .r3, mov .r21 .r4, mov .r22 .r5, mov .r23 .r6])) s (PkInv s) := by
  obtain hF : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine save_ok (by decide) (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu _ hsv hfr => ?_
  unfold mov
  refine wp_addi (by decide) (by decide) fun u₁ h₁ => wp_addi (by decide) (by decide) fun u₂ h₂ =>
    wp_addi (by decide) (by decide) fun u₃ h₃ => wp_addi (by decide) (by decide) fun u₄ h₄ => WP.block_nil ?_
  obtain m : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g : ∀ r, r ≠ .r20 → r ≠ .r21 → r ≠ .r22 → r ≠ .r23 → u₄.gpr r = u.gpr r := fun r a b c d => by
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, r ≠ .r0 → u.gpr r = s.gpr r := fun r h => hu.gpr r (by simpa using h)
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
  obtain hFw : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hCw : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hOw : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold publicKeyWith
  refine WP.seq (WP.mono_syms (pkSetup_ok hp) fun t₁ h₁ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (hd t₁ h₁) fun t₄ ⟨h₄, dg⟩ sy₄ => ?_)
  -- The pruning, and the arguments of `scalar_base`.
  obtain hFr : ∀ d, d + 8 ≤ 144 → InRegions (t₄.rd ++ t₄.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) hd (by omega_using [hd])
  obtain hFw' : ∀ d, d + 8 ≤ 144 → InRegions t₄.wr (s.gpr .r6 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h₄.wr]; exact in_base hFw hd (by omega_using [hd])
  refine WP.seq (WP.of_syms <| prune_ok (f := .r23) (F := s.gpr .r6) (d := 0) (o := 64) (by decide) (by decide) (h₄.regs _ (by decide))
    (by decide) (by decide) (by decide) (fun k hk => hFr _ (by omega_using [hk])) (fun k hk => hFw' _ (by omega_using [hk]))
    fun u hu hfu hpr => ?_)
  unfold mov
  refine wp_addi (by decide) (by decide) fun v₁ e₁ => wp_addi (by decide) (by decide) fun v₂ e₂ =>
    wp_addi (by decide) (by decide) fun t₅ e₃ => WP.block_nil fun sy₅ => ?_
  obtain g₅ : ∀ r ∈ preserved, t₅.gpr r = t₄.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, -, -⟩ := pres_args hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, hu.gpr _ (by revert hr; cases r <;> decide)]
  obtain m₅ : t₅.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  obtain h₅ : PkInv s t₅ := h₄.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, hu.rd])
    (by rw [e₃.wr, e₂.wr, e₁.wr, hu.wr]) (by rw [e₃.sp, e₂.sp, e₁.sp, hu.sp]) g₅ (m₅ ▸ hfu)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, wF, Offset.sub_base _ (by decide)⟩)
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 64 32 (by decide)
  obtain c3 : t₅.gpr .r3 = s.gpr .r3 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, BitVec.add_zero, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  obtain c4 : t₅.gpr .r4 = s.gpr .r6 + BitVec.ofNat 64 64 := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hu.gpr _ (by decide), h₄.regs _ (by decide)]; rfl
  obtain c5 : t₅.gpr .r5 = s.gpr .r5 := by
    rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), BitVec.add_zero, hu.gpr _ (by decide),
      h₄.regs _ (by decide)]; rfl
  obtain hdec : decodeLE (bytesAt t₅.mem (s.gpr .r6 + BitVec.ofNat 64 64) 32) =
      Spec.Ed25519.prune (Spec.Sha512.sha512 seed) := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  obtain ce : ∀ q, q ∉ linkRegs → ∀ rd wr, (t₅.callEntry.withRegions rd wr).gpr q = t₅.gpr q :=
    fun q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain sc4 : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  obtain sy : t₅.syms combSym = s.syms combSym := by rw [sy₅, sy₄, sy₁]
  obtain wd₅ : ∀ q < 64 * 96, t₅.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q :=
    fun q hq => by
      rw [← hp.words q hq]
      exact h₅.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) hp.tW
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
  obtain h₆ : PkInv s t₆ := h₅.step pkRegs_pres a b c hg hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, wO, sub_refl _⟩
      · exact ⟨_, wC, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hsl₁
      · exact hsl₂
  -- The restores.
  obtain hrl : ∀ p ∈ restoreList 96 pkRegs, p.2 + 8 ≤ 144 := by decide
  refine restore_ok h₆ (by decide) (h₆.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₆.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₇ g₇ sp₇ lr₇ m₇ _ => ⟨g₇, sp₇, lr₇, ?_⟩
  rw [m₇, hpost, Spec.Ed25519.scalarBase, hdec]
  rfl

/-- The digest at `r4` copied to `0(F)`. -/
theorem pkCopy_ok {s t : State} (hp : PkPre 64 s) (h : PkInv s t) :
    WP isa (.block (copyIn64 .r21 .r23 0)) t fun t' => PkInv s t' ∧
      bytesAt t'.mem (s.gpr .r6) 64 = bytesAt s.mem (s.gpr .r4) 64 := by
  obtain ⟨-, -, -, hsl₄⟩ := pk_slot hp
  obtain ⟨-, -, wF, -⟩ := pk_inW (s := s)
  obtain hS : (⟨s.gpr .r4, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  obtain hFw : (⟨s.gpr .r6, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain F0 : Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 0, 64⟩ ⟨s.gpr .r6, 144⟩ := Offset.sub_base _ (by decide)
  rw [← List.append_nil (copyIn64 .r21 .r23 0)]
  refine copy64_ok (A := s.gpr .r4) (B := s.gpr .r6) (o := 0) (by decide) (by decide) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide) (by decide)
    (fun k hk => by rw [h.rd, h.wr]; exact in_base (List.mem_append_left _ hS) (by omega_using [hk]) (by omega_using [hk]))
    (fun k hk => by rw [h.wr]; exact in_base hFw (by omega_using [hk]) (by omega_using [hk]))
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

end

end

/-!
# `vg_ed25519_public_key_expanded` on PPC64LE, with its frame as an argument, verified

The code meets `publicKeyExpandedContract` under `abi.withConsts combConsts`
(the comb's table, which `vg_ed25519_scalar_base` reads) with the frame as one
more argument (`Sig.scratchContract`), and 48 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkCE`: `pkRE`
without the table, and what the table adds), which it implies
(`consts_implies`), and a state satisfying it, with the table at `0x100000`
(`tblMem`) and the digest at `r4` at `0x2000` (`satMemE`, which also holds the
seed's public key, for signing); and, in its frame, the contract itself
(`publicKeyExpanded_framed`). Only the pointers and the table's address are
public: the pointers stay in `r20`–`r23`, which no function called writes, so
the taint analysis (`taint_decide`, under `vectorTaintSym`) sees them public
throughout, callees included.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym combWords combConsts)
open VG.Proof.Ed25519.PPC64LE (combWords_length TBL tbl_of_consts rd_of_consts consts_implies base_ok)

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 48 ∈ PPC64LE.abi.reserved 48 s := by
  show _ ∈ stackBelow s.sp 48
  rw [stackBelow_pos _ (by decide)]; simp

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- The contract by register: `out` in `r3`, the seed's digest at `r4`, `scratch` in `r5`, the
frame in `r6`; without the comb's table. -/
def pkRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let dg : Region := ⟨s.gpr .r4, 64⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 144⟩
    s.rd = [dg] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint dg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      dg.Disjoint sc ∧ dg.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint dg ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey seed
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `pkRE` with the comb's table (`abi.withConsts`): `pkRE` for the state without it, and what the
table adds. -/
def pkCE : Contract isa where
  pre s := pkRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 48 s
  post := pkRE.post
  pub s₁ s₂ := pkRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem pkE_ok (B : BaseOk) (s : State) (hs : pkCE.pre s) :
    ∃ t s', Exec isa publicKeyExpanded s t s' ∧ abiPreserved s s' ∧ pkCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, seed, -, hsd⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 64⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ :=
    publicKeyExpanded_wp B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, tfit, words, tW⟩ hsd
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, fun seed' _ hs' => ?_⟩
  rw [hq]
  exact Proof.Ed25519.publicKey_of_sha512_eq (hsd.symm.trans hs')

theorem pkE_ct : ConstantTime isa pkCE.pre pkCE.pub publicKeyExpanded :=
  VG.Taint.constantTime (A := vectorTaintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun s₁ s₂ _ _ ⟨⟨p3, p4, p5, p6, psp⟩, hsy⟩ => ⟨⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- `publicKeyExpandedContract`'s precondition and postcondition. -/
def pkEPre (pb : Nat) : Curry (Proof.Ed25519.publicKeyExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed

def pkEPost (pb : Nat) : Proof.Ed25519.publicKeyExpandedSig.Post pb :=
  fun out expanded _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 32 = Spec.Ed25519.publicKey seed

theorem pkEPre_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (Proof.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Proof.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPre pb) vs m₁ →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Proof.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed at h
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1]
    exact h

theorem pkEPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Proof.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Proof.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m₁ m' r →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Proof.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 32 = Spec.Ed25519.publicKey seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1]
    exact h

theorem pkEPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Proof.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Proof.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₁ r →
    Curry.apply (Proof.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Proof.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 32 = Spec.Ed25519.publicKey seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.1]
    exact h

/-! ### A memory with a seed's digest and public key

The digest of `WholeLocal.satSeed` at `0x2000`, its public key at `0x2100`. -/

theorem satSeed_length : Proof.Ed25519.WholeLocal.satSeed.length = 32 := by
  simp only [Proof.Ed25519.WholeLocal.satSeed, bytesAt, List.length_map, List.length_range]

def satDigestE : List Byte := Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed

def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x2100 then satDigestE[a.toNat - 0x2000]?.getD 0
  else Proof.Ed25519.WholeLocal.satKey[a.toNat - 0x2100]?.getD 0

theorem sat_digestE : bytesAt satMemE 0x2000 64 = satDigestE := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, satDigestE, Proof.Ed25519.sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega_using [], show 0x2000 + i < 0x2100 from by omega_using [hi'], ite_false, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : bytesAt satMemE 0x2100 32 = Proof.Ed25519.WholeLocal.satKey := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, Proof.Ed25519.WholeLocal.satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2100 : Addr) + BitVec.ofNat 64 i).toNat = 0x2100 + i := by
      change (0x2100 + i % 2 ^ 64) % 2 ^ 64 = 0x2100 + i
      omega_using [hi']
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2100 + i < 0x2000 from by omega_using [], show ¬ 0x2100 + i < 0x2100 from by omega_using [], ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- `satMemE` below `0x100000`, the comb's table above. -/
@[irreducible] def satMemTE : Mem := fun a => if a.toNat < 0x100000 then satMemE a else tblMem a

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [combWords_length] at hi
  rw [← tblMem_held i (by rw [combWords_length]; exact hi)]
  refine Mem.readW_congr fun j hj => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [hi, hj]
  simp only [satMemTE, e, show ¬ 0x100000 + 8 * i + j < 0x100000 by omega_using [], ↓reduceIte]

theorem satMemTE_bytes {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x100000) :
    bytesAt satMemTE p n = bytesAt satMemE p n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [h, hi']
  simp only [satMemTE, e, show p.toNat + i < 0x100000 by omega_using [h, hi'], ↓reduceIte]

theorem satMemTE_digest : bytesAt satMemTE 0x2000 64 = Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed := by
  rw [satMemTE_bytes (by decide), sat_digestE]; rfl

/-! ### The contract -/

/-- A state satisfying the precondition, without the table. -/
def pkSatE : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := satMemE
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkRE_implies : pkRE.Implies (Sig.scratchContract PPC64LE.abi Proof.Ed25519.publicKeyExpandedSig "frame"
    .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits) true 48) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Proof.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Proof.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Proof.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        have hd : bytesAt satMemE 0x2000 64 = Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed := sat_digestE
        refine ⟨pkSatE, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Proof.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, PPC64LE.abi, PPC64LE.argRegs,
          pkSatE]
        sig_and_intros
        all_goals first
          | exact ⟨_, satSeed_length, hd⟩
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `pkSatE` with the table. -/
def pkSatCE : State :=
  { pkSatE with mem := satMemTE, rd := pkSatE.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkCE_sat : (Sig.scratchContract (PPC64LE.abi.withConsts combConsts) Proof.Ed25519.publicKeyExpandedSig
    "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits) true 48).pre pkSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, pkEPre, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions_cons,
    Abi.constRegions_nil,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkCE_implies : pkCE.Implies (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
    Proof.Ed25519.publicKeyExpandedSig "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits)
    true 48) :=
  consts_implies (kR := pkRE) pkRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatCE, pkCE_sat⟩

theorem publicKeyExpanded_verified :
    Verified PPC64LE.target publicKeyExpanded (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
      Proof.Ed25519.publicKeyExpandedSig "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits)
      true 48) :=
  Verified.of_correct (pkE_ok base_ok) pkE_ct pkCE_implies

/-- A state satisfying `vg_ed25519_public_key_expanded`'s precondition, without the frame. -/
def pkFrameSatE : State := { pkSatCE with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSatE_pre : ∃ s, (Proof.Ed25519.publicKeyExpandedContract (PPC64LE.abi.withConsts combConsts)
    (48 + 176)).pre s := by
  refine ⟨pkFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSatE = s
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 176 bytes, whose first 136 it zeroes before returning. -/
theorem publicKeyExpanded_framed :
    Verified PPC64LE.target publicKeyExpandedCode
      (Proof.Ed25519.publicKeyExpandedContract (PPC64LE.abi.withConsts combConsts) (48 + 176)) :=
  Verified.stackScratchWipedC (c₀ := (combSym, combWords)) (cs := []) (sig := Proof.Ed25519.publicKeyExpandedSig)
    (nm := "frame") (e := .u8) (n := 144) (pre := pkEPre PPC64LE.abi.ptrBits)
    (post := pkEPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 176)
    (words := 17) publicKeyExpanded_verified (by decide) (by decide) (by decide)
    (pkEPre_local _) (pkEPost_local _) (pkEPostOut_local _) pkFrameSatE_pre

end VG.Proof.Ed25519.PPC64LE.Whole
