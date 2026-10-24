module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed448_public_key` on PPC64LE, with its frame as an argument

`out` in `r3`, `seed` in `r4`, `scratch` in `r5` and the frame `F` (160
bytes) in `r6`: the registers saved at `120(F)`, `SHAKE256(seed, 114)` into
`F`, its first 57 bytes pruned in place, and `[s]B` encoded into `out` by a
call of `vg_ed448_scalar_base` (`publicKey_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea restore_ok restoreList)
open VG.Spec.Ed448 (bytesAt)

/-- The precondition, by register. -/
structure PkPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 57⟩]
  wr : s.wr = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 160⟩]
  oS : Region.Disjoint ⟨s.gpr .r3, 57⟩ ⟨s.gpr .r4, 57⟩
  oC : Region.Disjoint ⟨s.gpr .r3, 57⟩ ⟨s.gpr .r5, 8192⟩
  oF : Region.Disjoint ⟨s.gpr .r3, 57⟩ ⟨s.gpr .r6, 160⟩
  sC : Region.Disjoint ⟨s.gpr .r4, 57⟩ ⟨s.gpr .r5, 8192⟩
  sF : Region.Disjoint ⟨s.gpr .r4, 57⟩ ⟨s.gpr .r6, 160⟩
  cF : Region.Disjoint ⟨s.gpr .r5, 8192⟩ ⟨s.gpr .r6, 160⟩
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint ⟨s.gpr .r3, 57⟩
  bS : (below s.sp 48).Disjoint ⟨s.gpr .r4, 57⟩
  bC : (below s.sp 48).Disjoint ⟨s.gpr .r5, 8192⟩
  bF : (below s.sp 48).Disjoint ⟨s.gpr .r6, 160⟩

/-- What the body may write. -/
abbrev pkW (s : State) : List Region := [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r5, 8192⟩, ⟨s.gpr .r6, 160⟩, below s.sp 48]

/-- The values in `r20`–`r23`. -/
def pkV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r21 => s.gpr .r4 | .r22 => s.gpr .r5 | .r23 => s.gpr .r6 | _ => 0

abbrev PkInv (s : State) : State → Prop := Inv s (s.gpr .r6) 120 pkRegs (pkV s) (pkW s)

theorem pkRegs_pres : ∀ r ∈ pkRegs, r ∈ preserved := by decide

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem publicKey_wp (hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : PkPre s) :
    WP isa publicKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .r4) 57) := by
  have hFw : (⟨s.gpr .r6, 160⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hOw : (⟨s.gpr .r3, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsS : Region.Sub (slotArea (s.gpr .r6) 120 pkRegs) ⟨s.gpr .r6, 160⟩ := Offset.sub_base _ (by decide)
  have sl₁ : (slotArea (s.gpr .r6) 120 pkRegs).Disjoint ⟨s.gpr .r3, 57⟩ := hp.oF.symm.sub_left hsS
  have sl₂ : (slotArea (s.gpr .r6) 120 pkRegs).Disjoint ⟨s.gpr .r5, 8192⟩ := hp.cF.symm.sub_left hsS
  have sl₃ : (slotArea (s.gpr .r6) 120 pkRegs).Disjoint (below s.sp 48) := hp.bF.symm.sub_left hsS
  have sl₄ : ∀ d n, d + n ≤ 120 →
      (slotArea (s.gpr .r6) 120 pkRegs).Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 d, n⟩ := fun d n h =>
    Offset.disjoint _ (.inr h) (by decide) (by omega)
  have F0 : s.gpr .r6 + BitVec.ofNat 64 0 = s.gpr .r6 := BitVec.add_zero _
  have hF114 : Region.Sub ⟨s.gpr .r6, 114⟩ ⟨s.gpr .r6, 160⟩ := Region.sub_prefix (by decide)
  have hF57 : Region.Sub ⟨s.gpr .r6, 57⟩ ⟨s.gpr .r6, 160⟩ := Region.sub_prefix (by decide)
  unfold publicKey
  -- The setup.
  refine WP.seq (WP.mono (show WP isa (.block (saveRegs .r6 120 pkRegs ++
      ([(.r20, .r3), (.r21, .r4), (.r22, .r5), (.r23, .r6)] : List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ []))
      s (PkInv s) from setup_ok (by decide) (by decide) (by decide)
        (fun p hp' => in_base hFw (by revert p; decide) (by revert p; decide)) ⟨_, by simp, hsS⟩ rfl
        (by decide) (by decide) (fun p hp' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl | rfl | rfl <;> rfl) fun u hu => WP.block_nil hu) fun t₁ h₁ => ?_)
  have g21 : t₁.gpr .r21 = s.gpr .r4 := h₁.regs _ (by decide)
  have g22 : t₁.gpr .r22 = s.gpr .r5 := h₁.regs _ (by decide)
  have g23 : t₁.gpr .r23 = s.gpr .r6 := h₁.regs _ (by decide)
  have e₁ : KEnv (s.gpr .r5) t₁ := ⟨by rw [h₁.wr]; exact hCw, by rw [h₁.sp]; exact hp.sp, by rw [h₁.sp]; exact hp.bC⟩
  -- The hash.
  have pR : Piece.R t₁.gpr ⟨.r21, 0, .imm 57⟩ = ⟨s.gpr .r4, 57⟩ := by
    simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]
  have pk : PieceOk (s.gpr .r5) t₁ ⟨.r21, 0, .imm 57⟩ :=
    ⟨by decide, by decide, show 57 < 2 ^ 15 by decide, by
      rw [pR, h₁.rd, hp.rd]; exact fun a n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      by rw [pR]; exact hp.sC, by rw [pR, h₁.sp]; exact hp.bS⟩
  have hwF : PPC64LE.Covers [⟨s.gpr .r6, 114⟩] t₁.wr := by
    rw [h₁.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hFw, 0, by simp, by simp⟩
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r23) (o := 0) (out := s.gpr .r6) (by decide) (by decide)
    (by decide) g22 (by rw [g23, F0]) e₁ (by simp) (fun p hp' => by rw [List.mem_singleton.mp hp']; exact pk)
    hwF (hp.cF.symm.sub_left hF114) (by rw [h₁.sp]; exact hp.bF.sub_right hF114)) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ : PkInv s t₂ := Inv.kept h₁ pkRegs_pres k₂ (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨s.gpr .r6, 160⟩, by simp, hF114⟩
      · exact ⟨⟨s.gpr .r5, 8192⟩, by simp, sub_refl _⟩
      · exact ⟨below s.sp 48, by simp, by rw [h₁.sp]; exact sub_refl _⟩) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa using sl₄ 0 114 (by decide)
      · exact sl₂
      · rw [h₁.sp]; exact sl₃
  have seed₁ : Spec.Sha3.bytesAt t₁.mem (s.gpr .r4) 57 = bytesAt s.mem (s.gpr .r4) 57 :=
    bytes_keep h₁.frame (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.oS.symm
      · exact hp.sC
      · exact hp.sF
      · exact hp.bS.symm
  have hh : bytesAt t₂.mem (s.gpr .r6) 114 = Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114 := by
    have := d₂
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g21, BitVec.add_zero, seed₁] at this
    exact this
  -- The pruning, and the arguments of `scalar_base`.
  have hFw' : ∀ j < 57, InRegions t₂.wr (s.gpr .r6 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h₂.wr]; exact in_base hFw (by omega) (by omega)
  refine WP.seq (prune_ok (f := .r23) (o := 0) (q := s.gpr .r6) (by decide) (by decide) (by decide)
    (by rw [h₂.regs _ (by decide)]; exact F0) hFw' fun u um usp urd uwr ug => ?_)
  unfold mov
  refine wp_addi (by decide) (by decide) fun v₁ e₁ => wp_addi (by decide) (by decide) fun v₂ e₂ =>
    wp_addi (by decide) (by decide) fun t₃ e₃ => WP.block_nil ?_
  have m₃ : t₃.mem = pruned t₂.mem (s.gpr .r6) := by rw [e₃.mem, e₂.mem, e₁.mem, um]
  have h₃ : PkInv s t₃ := by
    refine h₂.step pkRegs_pres (by rw [e₃.rd, e₂.rd, e₁.rd, urd]) (by rw [e₃.wr, e₂.wr, e₁.wr, uwr])
      (by rw [e₃.sp, e₂.sp, e₁.sp, usp]) (fun r hr => ?_) (m₃ ▸ pruned_frame _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .r6, 160⟩, by simp, hF57⟩)
      fun r hr => by rw [List.mem_singleton.mp hr]; simpa using sl₄ 0 57 (by decide)
    obtain ⟨p0, p3, p4, p5, -, -, p8⟩ := pres_ne hr
    rw [e₃.other _ p5, e₂.other _ p4, e₁.other _ p3, ug _ p8]
  have c3 : t₃.gpr .r3 = s.gpr .r3 := by
    rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, BitVec.add_zero, ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  have c4 : t₃.gpr .r4 = s.gpr .r6 := by
    rw [e₃.other _ (by decide), e₂.gpr, BitVec.add_zero, e₁.other _ (by decide), ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  have c5 : t₃.gpr .r5 = s.gpr .r5 := by
    rw [e₃.gpr, BitVec.add_zero, e₂.other _ (by decide), e₁.other _ (by decide), ug _ (by decide),
      h₂.regs _ (by decide)]; rfl
  -- `scalar_base`.
  refine WP.seq (base_call hl c3 c4 c5 (hp.oF.sub_right hF57) hp.oC (hp.cF.symm.sub_left hF57)
    (fun a n ⟨r, hr, hc⟩ => by
      rw [h₃.rd, h₃.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Covers.of_sub (rs := [⟨s.gpr .r6, 57⟩]) (fun r hr => by
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
      · exact ⟨⟨s.gpr .r3, 57⟩, by simp, sub_refl _⟩
      · exact ⟨⟨s.gpr .r5, 8192⟩, by simp, sub_refl _⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sl₁
      · exact sl₂
  -- The restores.
  have hrl : ∀ p ∈ restoreList 120 pkRegs, p.2 + 8 ≤ 160 := by decide
  refine restore_ok h₄ (by decide) (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [h₄.wr]; exact in_base (List.mem_append_right _ hFw) (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ lr₅ m₅ _ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [m₅, hb, Spec.Ed448.scalarBase, m₃, pruned_prune, hh]
  rfl

end VG.Proof.Ed448.PPC64LE.Whole
