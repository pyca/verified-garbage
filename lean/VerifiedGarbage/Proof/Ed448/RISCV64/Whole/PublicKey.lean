module

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Calls
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Hash
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# `vg_ed448_public_key` on RISCV64, with its frame as an argument

`out` in `a0`, `seed` in `a1`, `scratch` in `a2` and the frame `F` (160
bytes) in `a3`: the registers saved at `120(F)`, `SHAKE256(seed, 114)` into
`F`, its first 57 bytes pruned in place, and `[s]B` encoded into `out` by a
call of `vg_ed448_scalar_base` (`publicKey_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea restore_ok restoreList)
open VG.Spec.Ed448 (bytesAt)

/-- The precondition, by register. -/
structure PkPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 57⟩]
  wr : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 160⟩]
  oS : Region.Disjoint ⟨s.gpr .a0, 57⟩ ⟨s.gpr .a1, 57⟩
  oC : Region.Disjoint ⟨s.gpr .a0, 57⟩ ⟨s.gpr .a2, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .a0, 57⟩ ⟨s.gpr .a3, 160⟩
  sC : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨s.gpr .a2, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨s.gpr .a3, 160⟩
  cF : Region.Disjoint ⟨s.gpr .a2, 8192⟩ ⟨s.gpr .a3, 160⟩
  alC : (s.gpr .a2).toNat % 8 = 0
  alF : (s.gpr .a3).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  bO : (below s.sp 1168).Disjoint ⟨s.gpr .a0, 57⟩
  bS : (below s.sp 1168).Disjoint ⟨s.gpr .a1, 57⟩
  bC : (below s.sp 1168).Disjoint ⟨s.gpr .a2, 8192⟩
  bF : (below s.sp 1168).Disjoint ⟨s.gpr .a3, 160⟩

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩, ⟨s.gpr .a3, 160⟩, below s.sp 1168]

/-- The values in `s7`–`s10`. -/
def pkV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a0 | .s8 => s.gpr .a1 | .s9 => s.gpr .a2 | .s10 => s.gpr .a3 | _ => 0

theorem pres_a {r : Reg} (h : r ∈ preserved) : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 := by
  revert r; decide

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .a3) 120 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem publicKey_wp (hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : PkPre s) :
    WP isa publicKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      bytesAt t.mem (s.gpr .a0) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .a1) 57) := by
  have hFw : (⟨s.gpr .a3, 160⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .a0, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsS : Region.Sub (slotArea (s.gpr .a3) 120 pkRegs) ⟨s.gpr .a3, 160⟩ := Offset.sub_base _ (by decide)
  have sl₁ : (slotArea (s.gpr .a3) 120 pkRegs).Disjoint ⟨s.gpr .a0, 57⟩ := hp.oF.symm.sub_left hsS
  have sl₂ : (slotArea (s.gpr .a3) 120 pkRegs).Disjoint ⟨s.gpr .a2, 8192⟩ := hp.cF.symm.sub_left hsS
  have sl₃ : (slotArea (s.gpr .a3) 120 pkRegs).Disjoint (below s.sp 1168) := hp.bF.symm.sub_left hsS
  have sl₄ : ∀ d n, d + n ≤ 120 →
      (slotArea (s.gpr .a3) 120 pkRegs).Disjoint ⟨s.gpr .a3 + BitVec.ofNat 64 d, n⟩ := fun d n h =>
    Offset.disjoint _ (.inr h) (by decide) (by omega)
  have F0 : s.gpr .a3 + BitVec.ofNat 64 0 = s.gpr .a3 := BitVec.add_zero _
  have hF114 : Region.Sub ⟨s.gpr .a3, 114⟩ ⟨s.gpr .a3, 160⟩ := Region.sub_prefix (by decide)
  have hF57 : Region.Sub ⟨s.gpr .a3, 57⟩ ⟨s.gpr .a3, 160⟩ := Region.sub_prefix (by decide)
  unfold publicKey
  -- The setup.
  refine WP.seq (WP.mono (show WP isa (.block (saveRegs .a3 120 pkRegs ++
      ([(.s7, .a0), (.s8, .a1), (.s9, .a2), (.s10, .a3)] : List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ []))
      s (PkInv s) from setup_ok hp.alF (by decide) (by decide)
        (fun p hp' => in_base hFw (by revert p; decide) (by revert p; decide)) ⟨_, by simp, hsS⟩ rfl
        (by decide) (by decide) (fun p hp' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl | rfl | rfl <;> rfl) fun u hu => WP.block_nil hu) fun t₁ h₁ => ?_)
  have g22x : t₁.gpr .s8 = s.gpr .a1 := h₁.regs _ (by decide)
  have g23x : t₁.gpr .s9 = s.gpr .a2 := h₁.regs _ (by decide)
  have g24x : t₁.gpr .s10 = s.gpr .a3 := h₁.regs _ (by decide)
  have e₁ : KEnv (s.gpr .a2) t₁ := ⟨by rw [h₁.wr]; exact hCw, hp.alC, by rw [h₁.sp]; exact hp.spal,
    by rw [h₁.sp]; exact hp.sp, by rw [h₁.sp]; exact hp.bC⟩
  -- The hash.
  have pR : Piece.R t₁.gpr ⟨.s8, 0, .imm 57⟩ = ⟨s.gpr .a1, 57⟩ := by
    simp only [Piece.R, Piece.addr, Len.val, g22x, BitVec.add_zero]
  have pk : PieceOk (s.gpr .a2) t₁ ⟨.s8, 0, .imm 57⟩ :=
    ⟨by decide, by decide, show 57 < 2048 by decide, by
      rw [pR, h₁.rd, hp.rd]; exact fun a n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      by rw [pR]; exact hp.sC, by rw [pR, h₁.sp]; exact hp.bS⟩
  have hwF : Covers [⟨s.gpr .a3, 114⟩] t₁.wr := by
    rw [h₁.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hFw, 0, by simp, by simp⟩
  refine WP.seq (WP.mono (hash_ok (sc := .s9) (f := .s10) (o := 0) (out := s.gpr .a3) (by decide) (by decide)
    (by decide) g23x (by rw [g24x, F0]) e₁ (by simp) (fun p hp' => by rw [List.mem_singleton.mp hp']; exact pk)
    hwF (hp.cF.symm.sub_left hF114) (by rw [h₁.sp]; exact hp.bF.sub_right hF114)) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ : PkInv s t₂ := Inv.kept h₁ pkRegs_pres k₂ (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨s.gpr .a3, 160⟩, by simp, hF114⟩
      · exact ⟨⟨s.gpr .a2, 8192⟩, by simp, sub_refl _⟩
      · exact ⟨below s.sp 1168, by simp, by rw [h₁.sp]; exact sub_refl _⟩) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa using sl₄ 0 114 (by decide)
      · exact sl₂
      · rw [h₁.sp]; exact sl₃
  have seed₁ : Spec.Sha3.bytesAt t₁.mem (s.gpr .a1) 57 = bytesAt s.mem (s.gpr .a1) 57 :=
    bytes_keep h₁.frame (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.oS.symm
      · exact hp.sC
      · exact hp.sF
      · exact hp.bS.symm
  have hh : bytesAt t₂.mem (s.gpr .a3) 114 = Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .a1) 57) 114 := by
    have := d₂
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g22x, BitVec.add_zero, seed₁] at this
    exact this
  -- The pruning, and the arguments of `scalar_base`.
  have hFw' : ∀ j < 57, InRegions t₂.wr (s.gpr .a3 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h₂.wr]; exact in_base hFw (by omega) (by omega)
  refine WP.seq (prune_ok (f := .s10) (o := 0) (q := s.gpr .a3) (by decide) (by decide)
    (by rw [h₂.regs _ (by decide)]; exact F0) hFw' fun u um usp urd uwr ug => ?_)
  unfold mov
  refine wp_mv fun v₁ e₁ => wp_mv fun v₂ e₂ => wp_mv fun t₃ e₃ => WP.block_nil ?_
  have m₃ : t₃.mem = pruned t₂.mem (s.gpr .a3) := by rw [e₃.mem, e₂.mem, e₁.mem, um]
  have h₃ : PkInv s t₃ := by
    refine h₂.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, urd]) (by rw [e₃.wr, e₂.wr, e₁.wr, uwr])
      (by rw [e₃.sp, e₂.sp, e₁.sp, usp]) (fun r hr => ?_) (m₃ ▸ pruned_frame _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .a3, 160⟩, by simp, hF57⟩)
      fun r hr => by rw [List.mem_singleton.mp hr]; simpa using sl₄ 0 57 (by decide)
    obtain ⟨p3, p4, p5, p8⟩ := pres_a hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, ug _ p8]
  have c3 : t₃.gpr .a0 = s.gpr .a0 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  have c4 : t₃.gpr .a1 = s.gpr .a3 := by
    rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  have c5 : t₃.gpr .a2 = s.gpr .a2 := by
    rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  -- `scalar_base`.
  refine WP.seq (base_call hl c3 c4 c5 (hp.oF.sub_right hF57) hp.oC (hp.cF.symm.sub_left hF57)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₃.rd, h₃.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Covers.of_sub (rs := [⟨s.gpr .a3, 57⟩]) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hFw, 0, by simp, by simp⟩) a n
          ⟨_, List.mem_singleton_self _, hc⟩
      · exact ⟨_, List.mem_append_right _ hOw, hc⟩
      · exact ⟨_, List.mem_append_right _ hCw, hc⟩)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₃.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hOw, hc⟩
      · exact ⟨_, hCw, hc⟩) fun t₄ a b c f g hb => ?_)
  have h₄ : PkInv s t₄ := h₃.step pkRegs_pres a b c g f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .a0, 57⟩, by simp, sub_refl _⟩
      · exact ⟨⟨s.gpr .a2, 8192⟩, by simp, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sl₁
      · exact sl₂
  -- The restores.
  have hrl : ∀ p ∈ restoreList 120 pkRegs, p.2 + 8 ≤ 160 := by decide
  refine restore_ok h₄ hp.alF (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ ra₅ m₅ _ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [m₅, hb, Spec.Ed448.scalarBase, m₃, pruned_prune, hh]
  rfl

end VG.Proof.Ed448.RISCV64.Whole
