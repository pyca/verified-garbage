module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoop
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBodyD
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadD
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Lane0Zero
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# The loops over the blocks after the last group, decrypted

`remLoopsD_ok`: the loops of `StitchZH.remLoopsD`, over the `r` blocks at
`S` (read through `src`), their keystream at `P + 768` and their powers at
`W`, write their decryption to `A` (`REnv.X`: the block and its keystream
added, as for encryption) and leave in `Y` the products of the blocks as
read (`REnv.H`) with their powers (`Y` added to the first), reduced and
added. As `remLoops_ok`, with `remStep1D_ok` and `remStep4D_ok`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZH (remBodyD remNext1 remQuadD remNext4 remLoopsD)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Proof.Gcm.X86_64.StitchZ (fin_ok)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- Block `j`, as read: what decryption hashes. -/
abbrev REnv.H (E : REnv) (j : Nat) : Block := blockAt E.m (E.aS j)

/-- After the first `i` of the `r mod 4` blocks that go one at a time. -/
structure RInv1D (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r % 4
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = laneAcc E.H E.T E.y E.r 0 i
  zhi : ∀ l, 1 ≤ l → l < 4 → t.zlane .xmm8 l = 0 ∧ t.zlane .xmm9 l = 0 ∧ t.zlane .xmm10 l = 0
  y : ∀ l < 4, t.zlane .xmm2 l = if i + l = 0 then E.y else 0
  m0 : ∀ l < 4, t.zlane .xmm0 l = revMask
  m1 : ∀ l < 4, t.zlane .xmm1 l = poly

/-- After the first `i` blocks, `i - r mod 4` of them four at a time. -/
structure RInv4D (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  k : E.r % 4 ≤ i
  md : (i - E.r % 4) % 4 = 0
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : ∀ l < 4, prod (t.zproj l) = laneAcc E.H E.T E.y E.r l i
  y : ∀ l < 4, t.zlane .xmm2 l = if i + l = 0 then E.y else 0
  m0 : ∀ l < 4, t.zlane .xmm0 l = revMask
  m1 : ∀ l < 4, t.zlane .xmm1 l = poly

/-- After the loops and the reduction. -/
structure RPostD (E : REnv) (t : State) : Prop where
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * E.r⟩] E.m t.mem
  ct : ∀ j < E.r, blockAt t.mem (E.aD j) = E.X j
  y : t.lane .xmm2 0 =
    (reduceB (laneAcc E.H E.T E.y E.r 0 E.r) ^^^ reduceB (laneAcc E.H E.T E.y E.r 2 E.r)) ^^^
      (reduceB (laneAcc E.H E.T E.y E.r 1 E.r) ^^^ reduceB (laneAcc E.H E.T E.y E.r 3 E.r))
  m0 : t.lane .xmm0 0 = revMask


/-- One block, to lane 0. -/
theorem remStep1D_ok {E : REnv} (hE : E.Ok) {i : Nat} (hi : i < E.r % 4) {t : State} (hI : RInv1D E i t) :
    WP isa (.block (remBodyD E.src ++ remNext1)) t fun t' =>
      RInv1D E (i + 1) t' ∧ t'.zf = some (decide (E.r % 4 = i + 1)) := by
  have r15 := hE.r15
  have hir : i < E.r := by omega
  have gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10, hE.gS]
  have gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide), hE.gA]
  have gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide), hE.gP]
  have gW : t.gpr .rax = E.W := by rw [hI.gpr _ (by decide) (by decide), hE.gW]
  have eS : t.gpr E.src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS i := by rw [gS, hI.r10, addr0]
  have eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  have eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  have eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aW i := by rw [gW, hI.r10, addr0]
  have dD : ∀ j < E.r, Region.Sub ⟨E.aD j, 16⟩ ⟨E.A, 16 * E.r⟩ := fun j hj => Offset.sub_base _ (by omega)
  have dDW : Region.Disjoint ⟨E.aD i, 16⟩ ⟨E.aW i, 16⟩ := (hE.dW i hir).symm.sub_left (dD i hir)
  have sDW : Mem.Sep (E.aD i) 16 (E.aW i) 16 := dDW.sep (Region.contains_self _ _) (Region.contains_self _ _)
  have fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ r' ∈ [(⟨E.A, 16 * i⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Region.sub_prefix (by omega))
  have bS : blockAt t.mem (E.aS i) = blockAt E.m (E.aS i) := blockAt_frame hI.frame fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS i hir i (Nat.le_refl _)
  have bK : blockAt t.mem (E.aK i) = blockAt E.m (E.aK i) := blockAt_frame hI.frame (fA _ (hE.dK i hir))
  have rW : t.mem.readW (E.aW i) 128 = E.T i :=
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dW i hir)) (by decide)
  have h0 : (t.proj 0).xmm .xmm0 = revMask := by
    rw [State.proj_xmm, ← State.zlane_lt2 _ _ (by decide)]; exact hI.m0 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.lane0z (lane0_remBodyD E.src) (remSseD_ok E.src (t.proj 0) h0
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eS, hI.rd, hI.wr]; exact hE.inS i hir)
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eK, hI.rd, hI.wr]; exact hE.inK i hir)
    (by rw [State.proj_gpr, State.proj_wr, eD, hI.wr]; exact hE.inD i hir)
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eW, hI.rd, hI.wr]; exact hE.inW i hir)
    (by rw [State.proj_gpr, eD, eW]; exact sDW)))
    fun t₁ ⟨⟨m₁, p₁, y₁, rd₁, wr₁, k₁⟩, hg, hz, hk⟩ => ?_
  have g₁ : t₁.gpr = t.gpr := hg (remBodyD_noGpr E.src)
  simp only [State.proj_mem, State.proj_gpr, State.proj_rd, State.proj_wr, State.proj_xmm] at m₁ p₁ y₁ rd₁ wr₁
  rw [eD, eS, eK] at m₁
  rw [eS, eW] at p₁
  have hX : XBinOp.eval .pshufb (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aS i) 128) revMask = E.X i := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK, BitVec.xor_comm]
  have hH : XBinOp.eval .pshufb (t.mem.readW (E.aS i) 128) revMask = E.H i := by
    rw [← blockAt_eq, bS]
  refine WP.mono (remNext1_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, zl, mm, rd', wr'⟩ => ⟨?_, ?_⟩
  · have m' : t'.mem = t.mem.writeW (E.aD i) (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aS i) 128) := by
      rw [mm, m₁]
    have nd : ∀ r, r ∉ remRegs → r ∉ (remBodyD E.src).filterMap vdst := remBodyD_dst E.src
    refine ⟨by omega, a10, by rw [a9, show E.r - i - 1 = E.r - (i + 1) by omega],
      fun q h9 h10 => by rw [gg q h9 h10, g₁]; exact hI.gpr q h9 h10, by rw [rd', rd₁, hI.rd],
      by rw [wr', wr₁, hI.wr], ?_, fun j hj => ?_, ?_, fun l h1 h4 => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_⟩
    · rw [m']
      exact (hI.frame.sub fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    · rw [m']
      by_cases hji : j < i
      · rw [show E.aD i = (⟨E.aD i, 16⟩ : Region).base from rfl,
          blockAt_writeW_sep' (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) rfl]
        exact hI.ct j hji
      · obtain rfl : j = i := by omega
        rw [blockAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hX]
    · have e : prod (t'.proj 0) = prod (t₁.proj 0) := by
        simp only [prod, State.proj_xmm, ln]
      rw [e, p₁, hI.prod, hH, rW, ← State.zlane_lt2 _ _ (by decide), hI.y 0 (by decide), laneAcc_lo hi,
        Nat.add_zero, BitVec.xor_comm]
    · obtain ⟨z8, z9, z10⟩ := hI.zhi l h1 h4
      exact ⟨by rw [zl]; exact hz _ _ h1 h4 z8, by rw [zl]; exact hz _ _ h1 h4 z9,
        by rw [zl]; exact hz _ _ h1 h4 z10⟩
    · rw [zl]
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · rw [State.zlane_lt2 _ _ (by decide), y₁, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
      · rw [hz _ _ hl0 hl (by rw [hI.y l hl, ite_eq_right_iff.2 (fun h => absurd h (by omega))]),
          ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    · rw [zl, hk .xmm0 (nd _ (by decide)) l hl]; exact hI.m0 l hl
    · rw [zl, hk .xmm1 (nd _ (by decide)) l hl]; exact hI.m1 l hl
  · rw [z]; congr 1; simp only [decide_eq_decide]; omega

/-- Four blocks, one to each lane. -/
theorem remStep4D_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {i : Nat} (hi : i < E.r) {t : State} (hI : RInv4D E i t) :
    WP isa (.block (remQuadD E.src ++ remNext4)) t fun t' =>
      RInv4D E (i + 4) t' ∧ t'.zf = some (decide (E.r = i + 4)) := by
  have r15 := hE.r15
  have hle := hI.le
  have hk := hI.k
  have hmd := hI.md
  have hi4 : i + 4 ≤ E.r := by omega
  have gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10, hE.gS]
  have gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide), hE.gA]
  have gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide), hE.gP]
  have gW : t.gpr .rax = E.W := by rw [hI.gpr _ (by decide) (by decide), hE.gW]
  have eS : t.gpr E.src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS i := by rw [gS, hI.r10, addr0]
  have eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  have eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  have eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aW i := by rw [gW, hI.r10, addr0]
  have dDW : Region.Disjoint ⟨E.aD i, 64⟩ ⟨E.aW i, 64⟩ :=
    (h4.dW4 i hi4).symm.sub_left (Offset.sub_base _ (by omega))
  have fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ r' ∈ [(⟨E.A, 16 * i⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Region.sub_prefix (by omega))
  -- What the step reads, as it was before the loops.
  have rS : ∀ l < 4, t.mem.readW (E.aS (i + l)) 128 = E.m.readW (E.aS (i + l)) 128 := fun l hl =>
    hI.frame.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS (i + l) (by omega) i (by omega)) (by decide)
  have rK : ∀ l < 4, t.mem.readW (E.aK (i + l)) 128 = E.m.readW (E.aK (i + l)) 128 := fun l hl =>
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dK (i + l) (by omega))) (by decide)
  have rW : ∀ l < 4, t.mem.readW (E.aW (i + l)) 128 = E.T (i + l) := fun l hl =>
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dW (i + l) (by omega))) (by decide)
  have hX : ∀ l < 4, XBinOp.eval .pshufb (t.mem.readW (E.aK (i + l)) 128 ^^^ t.mem.readW (E.aS (i + l)) 128)
      revMask = E.X (i + l) := fun l hl => by
    rw [pshufb_rev_xor, rS l hl, rK l hl, ← blockAt_eq, ← blockAt_eq, BitVec.xor_comm]
  have hH : ∀ l < 4, XBinOp.eval .pshufb (t.mem.readW (E.aS (i + l)) 128) revMask = E.H (i + l) := fun l hl => by
    rw [rS l hl, ← blockAt_eq]
  rw [WP.block_append_iff]
  refine WP.mono (remQuadD_ok E.src t hI.m0 (by rw [eS, hI.rd, hI.wr]; exact h4.inS4 i hi4)
    (by rw [eK, hI.rd, hI.wr]; exact h4.inK4 i hi4) (by rw [eD, hI.wr]; exact h4.inD4 i hi4)
    (by rw [eW, hI.rd, hI.wr]; exact h4.inW4 i hi4) (by rw [eD, eW]; exact dDW))
    fun t₁ ⟨⟨v, m₁⟩, b₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD] at m₁ b₁
  rw [eS, eK] at b₁
  rw [eS] at p₁
  rw [eW] at p₁
  refine WP.mono (remNext4_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, zl, mm, rd', wr'⟩ => ⟨?_, ?_⟩
  · refine ⟨by omega, by omega, by omega, a10, by rw [a9, show E.r - i - 4 = E.r - (i + 4) by omega],
      fun q h9 h10 => by rw [gg q h9 h10, g₁]; exact hI.gpr q h9 h10, by rw [rd', rd₁, hI.rd],
      by rw [wr', wr₁, hI.wr], ?_, fun j hj => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_⟩
    · rw [mm, m₁]
      exact (hI.frame.sub fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    · rw [mm]
      by_cases hji : j < i
      · rw [m₁, show E.aD i = (⟨E.aD i, 64⟩ : Region).base from rfl,
          blockAt_writeW_sep' (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) rfl]
        exact hI.ct j hji
      · obtain ⟨l, rfl, hl⟩ : ∃ l, j = i + l ∧ l < 4 := ⟨j - i, by omega, by omega⟩
        have := b₁ l hl
        rw [addrL, addrL, addrLK] at this
        rw [this, hX l hl]
    · have e : prod (t'.zproj l) = prod (t₁.zproj l) := by
        simp only [prod, State.zproj_xmm, zl]
      rw [e, p₁ l hl, hI.prod l hl, hI.y l hl, addrL, hH l hl, addrL, rW l hl, laneAcc_quad hk hmd hl]
    · rw [zl, y₁ l hl, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    · rw [zl, k₁ .xmm0 (by decide) l hl]; exact hI.m0 l hl
    · rw [zl, k₁ .xmm1 (by decide) l hl]; exact hI.m1 l hl
  · rw [z]; congr 1; simp only [decide_eq_decide]; omega

/-- The single blocks, if any. -/
theorem loop1D_ok {E : REnv} (hE : E.Ok) {t : State} (hI : RInv1D E 0 t) (hk : E.r % 4 ≠ 0) :
    WP isa (.loop (.block (remBodyD E.src ++ remNext1)) .ne) t (RInv1D E (E.r % 4)) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r % 4 - i ∧ i < E.r % 4 ∧ RInv1D E i s) ?_ (E.r % 4) t
    ⟨0, rfl, by omega, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStep1D_ok hE hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r % 4 = i + 1
  · refine .inl ⟨by simp [eval, hz, h1], ?_⟩
    rwa [h1]
  · exact .inr ⟨by simp [eval, hz, h1], E.r % 4 - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩

/-- The blocks four at a time, if any. -/
theorem loop4D_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {k : Nat} {t : State} (hI : RInv4D E k t) (hk : k < E.r) :
    WP isa (.loop (.block (remQuadD E.src ++ remNext4)) .ne) t (RInv4D E E.r) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r - i ∧ i < E.r ∧ RInv4D E i s) ?_ (E.r - k) t
    ⟨k, rfl, hk, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStep4D_ok hE h4 hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h4 : E.r = i + 4
  · refine .inl ⟨by simp [eval, hz, h4], ?_⟩
    rwa [h4]
  · have := hI'.le
    exact .inr ⟨by simp [eval, hz, h4], E.r - (i + 4), by omega, i + 4, rfl, by omega, hI'⟩

/-- After the single blocks, the lanes are those of `RInv4`. -/
theorem RInv1D.toQuad {E : REnv} {t : State} (h : RInv1D E (E.r % 4) t) (hr : E.r % 4 ≤ E.r) :
    RInv4D E (E.r % 4) t :=
  { le := hr, k := Nat.le_refl _, md := by simp, r10 := h.r10, r9 := h.r9, gpr := h.gpr, rd := h.rd,
    wr := h.wr, frame := h.frame, ct := h.ct
    prod := fun l hl => by
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · rw [← h.prod]
        simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.zproj_xmm, State.proj_xmm, State.zlane_lt2 _ _ (show 0 < 2 by decide)]
      · obtain ⟨z8, z9, z10⟩ := h.zhi l hl0 hl
        rw [laneAcc_hi hl0 _ (Nat.le_refl _)]
        simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.zproj_xmm, z8, z9, z10]
        rfl
    y := h.y, m0 := h.m0, m1 := h.m1 }


theorem RInv1D.keep {E : REnv} {i : Nat} {t t' : State} (h : RInv1D E i t) (hg : t'.gpr = t.gpr)
    (hz : ∀ x l, t'.zlane x l = t.zlane x l) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    RInv1D E i t' :=
  { le := h.le, r10 := by rw [hg]; exact h.r10, r9 := by rw [hg]; exact h.r9,
    gpr := fun q h9 h10 => by rw [hg]; exact h.gpr q h9 h10, rd := by rw [hrd]; exact h.rd,
    wr := by rw [hwr]; exact h.wr, frame := by rw [hm]; exact h.frame, ct := fun j hj => by rw [hm]; exact h.ct j hj
    prod := by
      rw [← h.prod]
      have e : ∀ x, t'.lane x 0 = t.lane x 0 := fun x => by
        rw [← State.zlane_lt2 _ _ (by decide), ← State.zlane_lt2 _ _ (by decide), hz]
      simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.proj_xmm, e]
    zhi := fun l h1 h4 => by rw [hz, hz, hz]; exact h.zhi l h1 h4
    y := fun l hl => by rw [hz]; exact h.y l hl
    m0 := fun l hl => by rw [hz]; exact h.m0 l hl
    m1 := fun l hl => by rw [hz]; exact h.m1 l hl }

theorem RInv4D.keep {E : REnv} {i : Nat} {t t' : State} (h : RInv4D E i t) (hg : t'.gpr = t.gpr)
    (hz : ∀ x l, t'.zlane x l = t.zlane x l) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    RInv4D E i t' :=
  { le := h.le, k := h.k, md := h.md, r10 := by rw [hg]; exact h.r10, r9 := by rw [hg]; exact h.r9,
    gpr := fun q h9 h10 => by rw [hg]; exact h.gpr q h9 h10, rd := by rw [hrd]; exact h.rd,
    wr := by rw [hwr]; exact h.wr, frame := by rw [hm]; exact h.frame, ct := fun j hj => by rw [hm]; exact h.ct j hj
    prod := fun l hl => by rw [← h.prod l hl]; simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.zproj_xmm, hz]
    y := fun l hl => by rw [hz]; exact h.y l hl
    m0 := fun l hl => by rw [hz]; exact h.m0 l hl
    m1 := fun l hl => by rw [hz]; exact h.m1 l hl }

/-- The loops over the `r` blocks, and the four lanes' products reduced and added into `Y`. -/
theorem remLoopsD_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {t : State} (hI : RInv1D E 0 t) :
    WP isa (remLoopsD E.src) t (RPostD E) := by
  have r1 := hE.r1
  have r15 := hE.r15
  refine WP.seq (WP.mono (test9_ok t (r := E.r) (by omega) (by rw [hI.r9, Nat.sub_zero]))
    fun t₁ ⟨z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  have hI₁ := hI.keep g₁ l₁ m₁ rd₁ wr₁
  refine WP.seq (WP.mono (Q := RInv4D E (E.r % 4)) (WP.ite (decide (E.r % 4 = 0)) (by simp only [eval, z₁])
    (fun h => WP.block_nil ?_) (fun h => WP.mono (loop1D_ok hE hI₁ (by simpa using h))
      fun t₂ h₂ => h₂.toQuad (Nat.mod_le _ _))) fun t₂ hI₂ => ?_)
  · have h0 : E.r % 4 = 0 := by simpa using h
    have hI₁' : RInv1D E (E.r % 4) t₁ := by rw [h0]; exact hI₁
    exact hI₁'.toQuad (Nat.mod_le _ _)
  refine WP.seq (WP.mono (cmp16_ok t₂) fun t₃ ⟨z₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have hI₃ := hI₂.keep g₃ l₃ m₃ rd₃ wr₃
  have z₃' : t₃.zf = some (decide (E.r - E.r % 4 = 0)) := by
    rw [z₃, hI₂.r9]; exact congrArg some (sub16 _ (by omega))
  refine WP.seq (WP.mono (Q := RInv4D E E.r) (WP.ite (decide (E.r - E.r % 4 = 0)) (by simp only [eval, z₃'])
    (fun h => WP.block_nil ?_) (fun h => loop4D_ok hE h4 hI₃ (by simp at h; omega))) fun t₄ hI₄ => ?_)
  · have h0 : E.r % 4 = E.r := by simp at h; omega
    rw [h0] at hI₃; exact hI₃
  refine WP.mono (fin_ok t₄ hI₄.m1) fun t₅ ⟨y₅, _, f₅⟩ => ?_
  refine ⟨fun q h9 h10 => by rw [f₅.gpr]; exact hI₄.gpr q h9 h10, by rw [f₅.rd]; exact hI₄.rd,
    by rw [f₅.wr]; exact hI₄.wr, by rw [f₅.mem]; exact hI₄.frame, fun j hj => by rw [f₅.mem]; exact hI₄.ct j hj,
    ?_, ?_⟩
  · rw [← State.zlane_lt2 _ _ (by decide), y₅, hI₄.prod 0 (by decide), hI₄.prod 1 (by decide),
      hI₄.prod 2 (by decide), hI₄.prod 3 (by decide)]
  · rw [← State.zlane_lt2 _ _ (by decide), f₅.zlane _ (by decide) 0 (by decide)]
    exact hI₄.m0 0 (by decide)


end VG.Proof.Gcm.X86_64.StitchZH
