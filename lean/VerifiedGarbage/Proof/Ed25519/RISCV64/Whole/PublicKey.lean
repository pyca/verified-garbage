module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
public import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_public_key` on RISCV64, with its frame as an argument

`out` in `a0`, `seed` in `a1`, `scratch` in `a2` and the frame `F` (144
bytes) in `a3`: the registers saved at `96(F)`, the seed hashed into `F`, its
first half pruned into `64(F)`, and `[s]B` encoded into `out` by a call of
`vg_ed25519_scalar_base` (`publicKey_wp`). The body is proven once for any
first step that leaves the digest in `F` (`publicKeyWith_wp`): the hash, or,
for `vg_ed25519_public_key_expanded`, the copy of the digest at its second
argument (`publicKeyExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64 (combSym combWord)
open VG.Spec.Ed25519 (bytesAt decodeLE)

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩, below s.sp 208]

variable {sl : Nat}

/-- The precondition, by register, for `sl` bytes at `a1` (the seed, or its digest). -/
structure PkPre (sl : Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, sl⟩, TBL (s.syms combSym)]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 144⟩]
  oS : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a1, sl⟩
  oC : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a2, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 32⟩ ⟨s.gpr .a3, 144⟩
  sC : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a2, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, sl⟩ ⟨s.gpr .a3, 144⟩
  cF : Region.Disjoint ⟨s.gpr .a2, 8192⟩ ⟨s.gpr .a3, 144⟩
  alC : (s.gpr .a2).toNat % 8 = 0
  alF : (s.gpr .a3).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 208 ≤ s.sp.toNat
  bO : (below s.sp 208).Disjoint ⟨s.gpr .a0, 32⟩
  bS : (below s.sp 208).Disjoint ⟨s.gpr .a1, sl⟩
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
theorem pk_slot {s : State} (hp : PkPre sl s) :
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a0, 32⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a2, 8192⟩ ∧
    (slotArea (s.gpr .a3) 96 pkRegs).Disjoint (below s.sp 208) ∧
    ∀ d n, d + n ≤ 96 → (slotArea (s.gpr .a3) 96 pkRegs).Disjoint ⟨s.gpr .a3 + BitVec.ofNat 64 d, n⟩ := by
  have hs : Region.Sub (slotArea (s.gpr .a3) 96 pkRegs) ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨(hp.oF.symm.sub_left hs), (hp.cF.symm.sub_left hs), (hp.bF.symm.sub_left hs), fun d n h => ?_⟩
  exact Offset.disjoint _ (.inr h) (by decide) (by omega)

/-- The setup: the registers saved, the pointers moved to `s7`–`s10`. -/
theorem pkSetup_ok {s : State} (hp : PkPre sl s) :
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

/-- The seed (or its digest), while the body runs. -/
theorem pk_seed {s t : State} (hp : PkPre sl s) (h : PkInv s t) (hn : sl < 2 ^ 64) :
    bytesAt t.mem (s.gpr .a1) sl = bytesAt s.mem (s.gpr .a1) sl :=
  bytes_keep h.frame hn fun r hr => by
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

/-- The seed hashed into `0(F)`. -/
theorem pkHash_ok (C : ShaOK) {s t₁ : State} (hp : PkPre 32 s) (h₁ : PkInv s t₁) :
    WP isa pkHash t₁ fun u => PkInv s u ∧
      bytesAt u.mem (s.gpr .a3) 64 = Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a1) 32) := by
  obtain ⟨-, hsl₂, hsl₃, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, -, wF, wB⟩ := pk_inW (s := s)
  have hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
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
  unfold pkHash
  -- `init`.
  refine WP.seq (hashInit_ok C (sr := .s9) (h₁.regs _ (by decide)) (env t₁ h₁)
    fun t₂ a b c f g hr₂ => ?_)
  have h₂ : PkInv s t₂ := scStep h₁ a b c g f
  -- `update` with the seed.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s8) (off := 0) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (env t₂ h₂)
    (fun a n hi => by obtain ⟨r, hr, hc⟩ := hi; rw [h₂.rd, hp.rd]
                      exact ⟨r, List.mem_append_left _ (by simp at hr; simp [hr]), hc⟩)
    hp.sC (by rw [h₂.sp]; exact hp.bS) fun t₃ a b c f g hr₃ => ?_)
  have h₃ : PkInv s t₃ := scStep h₂ a b c g f
  have r₃ : Repr t₃.mem (s.gpr .a2) (bytesAt s.mem (s.gpr .a1) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, pk_seed hp h₂ (by decide)] at this
  -- `finalize` into `F`.
  refine hashFinalize_ok C (sr := .s9) (f := .s10) (o := 0) (out := s.gpr .a3) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (fun _ _ _ => rfl) (env t₃ h₃)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, h₃.wr]; exact ⟨_, hFw, 0, by simp, by simp⟩)
    (hp.cF.symm.sub_left (Region.sub_prefix (by decide)))
    (by rw [h₃.sp]; exact hp.bF.sub_right (Region.sub_prefix (by decide))) fun t₄ a b c f g hd₄ => ?_
  refine ⟨h₃.step pkRegs_pres a b c g f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, wC, sub_refl _⟩
      · exact ⟨_, wF, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by rw [h₃.sp]; exact wB, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hsl₂
      · simpa using hsl₄ 0 64 (by decide)
      · rw [h₃.sp]; exact hsl₃, hd₄ _ r₃ (by simp [bytesAt]) (by simp [bytesAt])⟩

/-- The seed's digest, at `expanded`, copied to `0(F)`. -/
theorem pkCopy_ok {s t : State} (hp : PkPre 64 s) (h : PkInv s t) :
    WP isa pkCopy t fun u => PkInv s u ∧ bytesAt u.mem (s.gpr .a3) 64 = bytesAt s.mem (s.gpr .a1) 64 := by
  obtain ⟨-, -, -, hsl₄⟩ := pk_slot hp
  have hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ t.wr := by rw [h.wr, hp.wr]; simp
  have hS : (⟨s.gpr .a1, 64⟩ : Region) ∈ t.rd := by rw [h.rd, hp.rd]; simp
  unfold pkCopy
  rw [← List.append_nil (copyIn .s8 .s10 0 64)]
  refine copyIn_ok (P := s.gpr .a1) (F := s.gpr .a3) (o := 0) (n := 64) (by decide) (by decide)
    (h.regs _ (by decide)) (h.regs _ (by decide)) (by decide)
    (fun i hi => in_base (List.mem_append_left _ hS) (by omega) (by omega))
    (fun i hi => in_base hFw (by omega) (by omega))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun u hu hfu hb => WP.block_nil ?_
  refine ⟨h.step pkRegs_pres hu.rd hu.wr hu.sp (fun r hr => hu.gpr r (by revert hr; cases r <;> decide)) hfu
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, pk_inW.2.2.1, Offset.sub_base _ (by decide)⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsl₄ 0 64 (by decide)), ?_⟩
  rw [BitVec.add_zero] at hb
  rw [hb, pk_seed hp h (by decide)]

/-- The body, from a first step that leaves the digest `D` at `0(F)`. -/
theorem publicKeyWith_wp (B : BaseOk) {first : Prog isa} {D : List Byte} {s : State} (hp : PkPre sl s)
    (hfirst : ∀ t, PkInv s t → WP isa first t fun u => PkInv s u ∧ bytesAt u.mem (s.gpr .a3) 64 = D) :
    WP isa (publicKeyWith first) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ bytesAt t.mem (s.gpr .a0) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune D) Spec.Ed25519.basePoint) := by
  obtain ⟨hsl₁, hsl₂, -, hsl₄⟩ := pk_slot hp
  obtain ⟨wC, wO, wF, -⟩ := pk_inW (s := s)
  have hFw : (⟨s.gpr .a3, 144⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold publicKeyWith
  refine WP.seq (WP.mono_syms (pkSetup_ok hp) fun t₁ h₁ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (hfirst t₁ h₁) fun t₄ ⟨h₄, dg⟩ sy₄ => ?_)
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
  have hdec : decodeLE (bytesAt t₅.mem (s.gpr .a3 + BitVec.ofNat 64 64) 32) = Spec.Ed25519.prune D := by
    rw [m₅, hpr, BitVec.add_zero, dg]
  -- `scalar_base`.
  have sc4 : Region.Sub ⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a3, 144⟩ := Offset.sub_base _ (by decide)
  have sy : t₅.syms combSym = s.syms combSym := by rw [sy₅, sy₄, sy₁]
  have wd₅ : ∀ q < 64 * 96, t₅.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 = combWord q :=
    fun q hq => by
      rw [← hp.words q hq]
      exact h₅.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega)) hp.tW
        (by decide)
  refine WP.seq (WP.call (k := baseRV) B (rd := [⟨s.gpr .a3 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
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

theorem publicKey_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : PkPre 32 s) :
    WP isa publicKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .a1) 32) :=
  WP.mono (publicKeyWith_wp B hp fun _ h => pkHash_ok C hp h) fun _ ⟨g, sp, ra, ho⟩ =>
    ⟨g, sp, ra, by rw [ho]; rfl⟩

/-- From the seed's digest at `expanded`: the public key of every seed with that digest. -/
theorem publicKeyExpanded_wp (B : BaseOk) {s : State} (hp : PkPre 64 s) :
    WP isa publicKeyExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ ∀ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
        bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey seed :=
  WP.mono (publicKeyWith_wp B (D := bytesAt s.mem (s.gpr .a1) 64) hp fun _ h => pkCopy_ok hp h) fun _ ⟨g, sp, ra, ho⟩ =>
    ⟨g, sp, ra, fun _ hs => by rw [ho, hs]; rfl⟩

end VG.Proof.Ed25519.RISCV64.Whole
