module

public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuad
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
public import VerifiedGarbage.Proof.Framework.X86_64.Lane0Zero
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The loops over the blocks after the last group

`remLoops_ok`: the loops of `StitchZH.remLoops`, over the `r` blocks at `S`
(read through `src`), their keystream at `P + 768` and their powers at `W`,
write their encryption to `A` and leave in `Y` their products with their
powers (`Y` added to the first), reduced and added. The first `r mod 4`
blocks go one at a time to lane 0 (`remStep1_ok`, `RInv1`), the rest four at
a time, one to each lane (`remStep4_ok`, `RInv4`): block `j` to lane
`laneOf r j`, whose products are `laneAcc`. `StitchZ.fin` reduces the four
lanes and adds them (`RPost`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZH (remBody remNext1 remQuad remNext4 remLoops)
open VG.Impl.Gcm.X86_64.StitchZ (fin)
open VG.Proof.Gcm.X86_64.StitchZ (fin_ok)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- The lane block `j` of the last `r` goes to: the first `r mod 4` to lane
0, the others four at a time, one to each lane. -/
def laneOf (r j : Nat) : Nat := if j < r % 4 then 0 else (j - r % 4) % 4

/-- The products in lane `l` of the first `n` of the last `r` blocks `X`
with their powers `T`, `y` added to the first. -/
def laneAcc (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) (r l : Nat) : Nat → Prod
  | 0 => Prod.zero
  | n + 1 => if laneOf r n = l then (laneAcc X T y r l n).acc ((if n = 0 then y else 0) ^^^ X n) (T n)
      else laneAcc X T y r l n

theorem laneAcc_congr {X X' : Nat → Block} {T T' : Nat → BitVec 128} (y : Block) (r l : Nat) :
    ∀ n, (∀ j < n, X j = X' j) → (∀ j < n, T j = T' j) → laneAcc X T y r l n = laneAcc X' T' y r l n
  | 0, _, _ => rfl
  | n + 1, hX, hT => by
    simp only [laneAcc]
    rw [laneAcc_congr y r l n (fun j hj => hX j (by omega)) (fun j hj => hT j (by omega)), hX n (by omega),
      hT n (by omega)]

/-- Lanes 1–3 have none of the first `r mod 4` blocks. -/
theorem laneAcc_hi {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r l : Nat} (hl : 1 ≤ l) :
    ∀ n, n ≤ r % 4 → laneAcc X T y r l n = Prod.zero
  | 0, _ => rfl
  | n + 1, hn => by
    have h0 : laneOf r n = 0 := by unfold laneOf; split <;> omega
    simp only [laneAcc, h0]
    split
    · omega
    · exact laneAcc_hi hl n (by omega)

/-- One of the first `r mod 4` blocks, to lane 0. -/
theorem laneAcc_lo {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r i : Nat} (hi : i < r % 4) :
    laneAcc X T y r 0 (i + 1) = (laneAcc X T y r 0 i).acc ((if i = 0 then y else 0) ^^^ X i) (T i) := by
  have h0 : laneOf r i = 0 := by unfold laneOf; split <;> omega
  simp only [laneAcc, h0, ite_true]

/-- Four blocks, one to each lane. -/
theorem laneAcc_quad {X : Nat → Block} {T : Nat → BitVec 128} {y : Block} {r i : Nat} (hk : r % 4 ≤ i)
    (hmd : (i - r % 4) % 4 = 0) {l : Nat} (hl : l < 4) :
    laneAcc X T y r l (i + 4) =
      (laneAcc X T y r l i).acc ((if i + l = 0 then y else 0) ^^^ X (i + l)) (T (i + l)) := by
  have h0 : laneOf r i = 0 := by unfold laneOf; split <;> omega
  have h1 : laneOf r (i + 1) = 1 := by unfold laneOf; split <;> omega
  have h2 : laneOf r (i + 2) = 2 := by unfold laneOf; split <;> omega
  have h3 : laneOf r (i + 3) = 3 := by unfold laneOf; split <;> omega
  rw [show i + 4 = i + 3 + 1 from rfl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
  simp only [laneAcc, h0, h1, h2, h3, Nat.add_zero, reduceCtorEq, ite_true, ite_false,
    show ¬ ((3 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 0) by decide,
    show ¬ ((1 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide, show ¬ ((2 : Nat) = 1) by decide,
    show ¬ ((0 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide, show ¬ ((1 : Nat) = 2) by decide,
    show ¬ ((0 : Nat) = 2) by decide, show ¬ ((2 : Nat) = 3) by decide, show ¬ ((1 : Nat) = 3) by decide,
    show ¬ ((0 : Nat) = 3) by decide]

namespace REnv
variable (E : REnv)

/-- What the loop over four blocks at a time needs of its regions, besides
`Ok`. -/
structure Ok4 : Prop where
  inS4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aS j) 64
  inK4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aK j) 64
  inD4 : ∀ j, j + 4 ≤ E.r → InRegions E.wr (E.aD j) 64
  inW4 : ∀ j, j + 4 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aW j) 64
  dW4 : ∀ j, j + 4 ≤ E.r → Region.Disjoint ⟨E.aW j, 64⟩ ⟨E.A, 16 * E.r⟩

end REnv


/-- After the first `i` of the `r mod 4` blocks that go one at a time. -/
structure RInv1 (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r % 4
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = laneAcc E.X E.T E.y E.r 0 i
  zhi : ∀ l, 1 ≤ l → l < 4 → t.zlane .xmm8 l = 0 ∧ t.zlane .xmm9 l = 0 ∧ t.zlane .xmm10 l = 0
  y : ∀ l < 4, t.zlane .xmm2 l = if i + l = 0 then E.y else 0
  m0 : ∀ l < 4, t.zlane .xmm0 l = revMask
  m1 : ∀ l < 4, t.zlane .xmm1 l = poly

/-- After the first `i` blocks, `i - r mod 4` of them four at a time. -/
structure RInv4 (E : REnv) (i : Nat) (t : State) : Prop where
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
  prod : ∀ l < 4, prod (t.zproj l) = laneAcc E.X E.T E.y E.r l i
  y : ∀ l < 4, t.zlane .xmm2 l = if i + l = 0 then E.y else 0
  m0 : ∀ l < 4, t.zlane .xmm0 l = revMask
  m1 : ∀ l < 4, t.zlane .xmm1 l = poly

/-- After the loops and the reduction. -/
structure RPost (E : REnv) (t : State) : Prop where
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * E.r⟩] E.m t.mem
  ct : ∀ j < E.r, blockAt t.mem (E.aD j) = E.X j
  y : t.lane .xmm2 0 =
    (reduceB (laneAcc E.X E.T E.y E.r 0 E.r) ^^^ reduceB (laneAcc E.X E.T E.y E.r 2 E.r)) ^^^
      (reduceB (laneAcc E.X E.T E.y E.r 1 E.r) ^^^ reduceB (laneAcc E.X E.T E.y E.r 3 E.r))
  m0 : t.lane .xmm0 0 = revMask

theorem addrL (p : Addr) (i l : Nat) :
    p + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (16 * (i + l)) := by
  rw [Offset.add_add, Nat.mul_add]

theorem addrLK (p : Addr) (i l : Nat) :
    p + BitVec.ofNat 64 (768 + 16 * i) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (768 + 16 * (i + l)) := by
  rw [Offset.add_add, Nat.mul_add, Nat.add_assoc]

/-- One block, to lane 0. -/
theorem remStep1_ok {E : REnv} (hE : E.Ok) {i : Nat} (hi : i < E.r % 4) {t : State} (hI : RInv1 E i t) :
    WP isa (.block (remBody E.src ++ remNext1)) t fun t' =>
      RInv1 E (i + 1) t' ∧ t'.zf = some (decide (E.r % 4 = i + 1)) := by
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
  refine WP.mono (WP.lane0z (lane0_remBody E.src) (remSse_ok E.src (t.proj 0) h0
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eS, hI.rd, hI.wr]; exact hE.inS i hir)
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eK, hI.rd, hI.wr]; exact hE.inK i hir)
    (by rw [State.proj_gpr, State.proj_wr, eD, hI.wr]; exact hE.inD i hir)
    (by rw [State.proj_gpr, State.proj_rd, State.proj_wr, eW, hI.rd, hI.wr]; exact hE.inW i hir)
    (by rw [State.proj_gpr, eD, eW]; exact sDW)))
    fun t₁ ⟨⟨m₁, p₁, y₁, rd₁, wr₁, k₁⟩, hg, hz, hk⟩ => ?_
  have g₁ : t₁.gpr = t.gpr := hg (remBody_noGpr E.src)
  simp only [State.proj_mem, State.proj_gpr, State.proj_rd, State.proj_wr, State.proj_xmm] at m₁ p₁ y₁ rd₁ wr₁
  rw [eD, eS, eK] at m₁
  rw [eS, eK, eW] at p₁
  have hX : XBinOp.eval .pshufb (t.mem.readW (E.aS i) 128 ^^^ t.mem.readW (E.aK i) 128) revMask = E.X i := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK]
  refine WP.mono (remNext1_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, zl, mm, rd', wr'⟩ => ⟨?_, ?_⟩
  · have m' : t'.mem = t.mem.writeW (E.aD i) (t.mem.readW (E.aS i) 128 ^^^ t.mem.readW (E.aK i) 128) := by
      rw [mm, m₁]
    have nd : ∀ r, r ∉ remRegs → r ∉ (remBody E.src).filterMap vdst := remBody_dst E.src
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
      rw [e, p₁, hI.prod, hX, rW, ← State.zlane_lt2 _ _ (by decide), hI.y 0 (by decide), laneAcc_lo hi,
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
theorem remStep4_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {i : Nat} (hi : i < E.r) {t : State} (hI : RInv4 E i t) :
    WP isa (.block (remQuad E.src ++ remNext4)) t fun t' =>
      RInv4 E (i + 4) t' ∧ t'.zf = some (decide (E.r = i + 4)) := by
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
  have hX : ∀ l < 4, XBinOp.eval .pshufb (t.mem.readW (E.aS (i + l)) 128 ^^^ t.mem.readW (E.aK (i + l)) 128)
      revMask = E.X (i + l) := fun l hl => by
    rw [pshufb_rev_xor, rS l hl, rK l hl, ← blockAt_eq, ← blockAt_eq]
  rw [WP.block_append_iff]
  refine WP.mono (remQuad_ok E.src t hI.m0 (by rw [eS, hI.rd, hI.wr]; exact h4.inS4 i hi4)
    (by rw [eK, hI.rd, hI.wr]; exact h4.inK4 i hi4) (by rw [eD, hI.wr]; exact h4.inD4 i hi4)
    (by rw [eW, hI.rd, hI.wr]; exact h4.inW4 i hi4) (by rw [eD, eW]; exact dDW))
    fun t₁ ⟨⟨v, m₁⟩, b₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD] at m₁ b₁
  rw [eS, eK] at b₁ p₁
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
      rw [e, p₁ l hl, hI.prod l hl, hI.y l hl, addrL, addrLK, hX l hl, addrL, rW l hl, laneAcc_quad hk hmd hl]
    · rw [zl, y₁ l hl, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    · rw [zl, k₁ .xmm0 (by decide) l hl]; exact hI.m0 l hl
    · rw [zl, k₁ .xmm1 (by decide) l hl]; exact hI.m1 l hl
  · rw [z]; congr 1; simp only [decide_eq_decide]; omega

/-- The single blocks, if any. -/
theorem loop1_ok {E : REnv} (hE : E.Ok) {t : State} (hI : RInv1 E 0 t) (hk : E.r % 4 ≠ 0) :
    WP isa (.loop (.block (remBody E.src ++ remNext1)) .ne) t (RInv1 E (E.r % 4)) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r % 4 - i ∧ i < E.r % 4 ∧ RInv1 E i s) ?_ (E.r % 4) t
    ⟨0, rfl, by omega, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStep1_ok hE hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r % 4 = i + 1
  · refine .inl ⟨by simp [eval, hz, h1], ?_⟩
    rwa [h1]
  · exact .inr ⟨by simp [eval, hz, h1], E.r % 4 - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩

/-- The blocks four at a time, if any. -/
theorem loop4_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {k : Nat} {t : State} (hI : RInv4 E k t) (hk : k < E.r) :
    WP isa (.loop (.block (remQuad E.src ++ remNext4)) .ne) t (RInv4 E E.r) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r - i ∧ i < E.r ∧ RInv4 E i s) ?_ (E.r - k) t
    ⟨k, rfl, hk, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStep4_ok hE h4 hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h4 : E.r = i + 4
  · refine .inl ⟨by simp [eval, hz, h4], ?_⟩
    rwa [h4]
  · have := hI'.le
    exact .inr ⟨by simp [eval, hz, h4], E.r - (i + 4), by omega, i + 4, rfl, by omega, hI'⟩

/-- After the single blocks, the lanes are those of `RInv4`. -/
theorem RInv1.toQuad {E : REnv} {t : State} (h : RInv1 E (E.r % 4) t) (hr : E.r % 4 ≤ E.r) :
    RInv4 E (E.r % 4) t :=
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

/-- `test r9, 3`: whether the blocks after the last group are a multiple of four. -/
theorem test9_ok (s : State) {r : Nat} (hr : r < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) :
    WP isa (.block [.alu .test .r9 (.imm 3)]) s fun s' =>
      s'.zf = some (decide (r % 4 = 0)) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    h9, test3 r hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `cmp r9, 16`: whether blocks are left after the last group. -/
theorem cmp16_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.zf = some (s.gpr .r9 - 16 == 0) ∧ s'.gpr = s.gpr ∧
        (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

theorem sub16 : ∀ m < 16, (BitVec.ofNat 64 (16 + m) - 16 == 0) = decide (m = 0) := by decide

theorem RInv1.keep {E : REnv} {i : Nat} {t t' : State} (h : RInv1 E i t) (hg : t'.gpr = t.gpr)
    (hz : ∀ x l, t'.zlane x l = t.zlane x l) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    RInv1 E i t' :=
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

theorem RInv4.keep {E : REnv} {i : Nat} {t t' : State} (h : RInv4 E i t) (hg : t'.gpr = t.gpr)
    (hz : ∀ x l, t'.zlane x l = t.zlane x l) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    RInv4 E i t' :=
  { le := h.le, k := h.k, md := h.md, r10 := by rw [hg]; exact h.r10, r9 := by rw [hg]; exact h.r9,
    gpr := fun q h9 h10 => by rw [hg]; exact h.gpr q h9 h10, rd := by rw [hrd]; exact h.rd,
    wr := by rw [hwr]; exact h.wr, frame := by rw [hm]; exact h.frame, ct := fun j hj => by rw [hm]; exact h.ct j hj
    prod := fun l hl => by rw [← h.prod l hl]; simp only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.zproj_xmm, hz]
    y := fun l hl => by rw [hz]; exact h.y l hl
    m0 := fun l hl => by rw [hz]; exact h.m0 l hl
    m1 := fun l hl => by rw [hz]; exact h.m1 l hl }

/-- The loops over the `r` blocks, and the four lanes' products reduced and added into `Y`. -/
theorem remLoops_ok {E : REnv} (hE : E.Ok) (h4 : E.Ok4) {t : State} (hI : RInv1 E 0 t) :
    WP isa (remLoops E.src) t (RPost E) := by
  have r1 := hE.r1
  have r15 := hE.r15
  refine WP.seq (WP.mono (test9_ok t (r := E.r) (by omega) (by rw [hI.r9, Nat.sub_zero]))
    fun t₁ ⟨z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_)
  have hI₁ := hI.keep g₁ l₁ m₁ rd₁ wr₁
  refine WP.seq (WP.mono (Q := RInv4 E (E.r % 4)) (WP.ite (decide (E.r % 4 = 0)) (by simp only [eval, z₁])
    (fun h => WP.block_nil ?_) (fun h => WP.mono (loop1_ok hE hI₁ (by simpa using h))
      fun t₂ h₂ => h₂.toQuad (Nat.mod_le _ _))) fun t₂ hI₂ => ?_)
  · have h0 : E.r % 4 = 0 := by simpa using h
    have hI₁' : RInv1 E (E.r % 4) t₁ := by rw [h0]; exact hI₁
    exact hI₁'.toQuad (Nat.mod_le _ _)
  refine WP.seq (WP.mono (cmp16_ok t₂) fun t₃ ⟨z₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have hI₃ := hI₂.keep g₃ l₃ m₃ rd₃ wr₃
  have z₃' : t₃.zf = some (decide (E.r - E.r % 4 = 0)) := by
    rw [z₃, hI₂.r9]; exact congrArg some (sub16 _ (by omega))
  refine WP.seq (WP.mono (Q := RInv4 E E.r) (WP.ite (decide (E.r - E.r % 4 = 0)) (by simp only [eval, z₃'])
    (fun h => WP.block_nil ?_) (fun h => loop4_ok hE h4 hI₃ (by simp at h; omega))) fun t₄ hI₄ => ?_)
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

/-- `StitchAvx.zero` (`VEX.128`) clears every lane of `xmm8` … `xmm10`. -/
theorem zeroZ_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' =>
      (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
      (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.StitchAvx.zero, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun x h8 h9 h10 l hl => ?_, rfl, rfl, rfl, rfl⟩
  · have z : ((if l = 0 then 0#128 else 0) : BitVec 128) = 0 := ite_self _
    simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hl, VBinOp.sse, Pclmul.eval_pxor, BitVec.xor_self,
      reduceCtorEq, ite_true, ite_false, z]
    exact ⟨trivial, trivial, trivial⟩
  · simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hl, h8, h9, h10, ite_false]

end VG.Proof.Gcm.X86_64.StitchZH
