import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBody
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# The loop over the blocks after the last group

`remLoop_ok`: the loop of `StitchZH.remWith`, over the `r` blocks at `S`
(read through `src`), their keystream at `P + 768` and their powers at `W`,
writes their encryption to `A`, and leaves in the lower lanes of `xmm8` …
`xmm10` the products of each (`Y` added to the first) with its power
(`accR`), as `RInv` says after each block.
-/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZH (remBody remNext)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- The products of the first `i` blocks `X` with their powers `T`, `y`
added to the first. -/
def accR (X : Nat → Block) (T : Nat → BitVec 128) (y : Block) : Nat → Prod
  | 0 => Prod.zero
  | i + 1 => (accR X T y i).acc ((if i = 0 then y else 0) ^^^ X i) (T i)

/-- What the loop does not change: the `r` blocks at `S` (read through
`src`), written to `A`, the working space at `P` (the keystream at
`P + 768`), the powers at `W`, the registers but `r9`, `r10` (`g`), the
memory before the loop and its regions. -/
structure REnv where
  r : Nat
  src : Reg
  S : Addr
  A : Addr
  P : Addr
  W : Addr
  m : Mem
  g : Reg → BitVec 64
  rd : List Region
  wr : List Region
  y : Block

namespace REnv
variable (E : REnv)

abbrev aS (j : Nat) : Addr := E.S + BitVec.ofNat 64 (16 * j)
abbrev aK (j : Nat) : Addr := E.P + BitVec.ofNat 64 (768 + 16 * j)
abbrev aD (j : Nat) : Addr := E.A + BitVec.ofNat 64 (16 * j)
abbrev aW (j : Nat) : Addr := E.W + BitVec.ofNat 64 (16 * j)
/-- Block `j`, encrypted. -/
abbrev X (j : Nat) : Block := blockAt E.m (E.aS j) ^^^ blockAt E.m (E.aK j)
abbrev T (j : Nat) : BitVec 128 := E.m.readW (E.aW j) 128

/-- What the loop needs of its regions. -/
structure Ok : Prop where
  r1 : 1 ≤ E.r
  r15 : E.r ≤ 15
  gS : E.g E.src = E.S
  gA : E.g .rdx = E.A
  gP : E.g .r11 = E.P
  gW : E.g .rax = E.W
  src9 : E.src ≠ .r9
  src10 : E.src ≠ .r10
  inS : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aS j) 16
  inK : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aK j) 16
  inD : ∀ j < E.r, InRegions E.wr (E.aD j) 16
  inW : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aW j) 16
  dS : ∀ j < E.r, ∀ i ≤ j, Region.Disjoint ⟨E.aS j, 16⟩ ⟨E.A, 16 * i⟩
  dK : ∀ j < E.r, Region.Disjoint ⟨E.aK j, 16⟩ ⟨E.A, 16 * E.r⟩
  dW : ∀ j < E.r, Region.Disjoint ⟨E.aW j, 16⟩ ⟨E.A, 16 * E.r⟩

end REnv

/-- After `i` of the `r` blocks. -/
structure RInv (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = accR E.X E.T E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  m0 : t.lane .xmm0 0 = revMask
  m1 : t.lane .xmm1 0 = poly

theorem addr0 (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 ((0 : Nat) : Int) = p + BitVec.ofNat 64 (16 * j) := by
  rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _

theorem addr768 (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 ((768 : Nat) : Int) = p + BitVec.ofNat 64 (768 + 16 * j) := by
  rw [BitVec.ofInt_natCast, Offset.add_add, Nat.add_comm]

/-- One block. -/
theorem remStep_ok {E : REnv} (hE : E.Ok) {i : Nat} (hi : i < E.r) {t : State} (hI : RInv E i t) :
    WP isa (.block (remBody E.src ++ remNext)) t fun t' =>
      RInv E (i + 1) t' ∧ t'.zf = some (decide (E.r - i = 1)) := by
  have r15 := hE.r15
  have gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10, hE.gS]
  have gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide), hE.gA]
  have gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide), hE.gP]
  have gW : t.gpr .rax = E.W := by rw [hI.gpr _ (by decide) (by decide), hE.gW]
  have eS : t.gpr E.src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS i := by rw [gS, hI.r10, addr0]
  have eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  have eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  have eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aW i := by rw [gW, hI.r10, addr0]
  have dD : ∀ j < E.r, Region.Sub ⟨E.aD j, 16⟩ ⟨E.A, 16 * E.r⟩ := fun j hj => Offset.sub_base _ (by omega)
  have dDW : Region.Disjoint ⟨E.aD i, 16⟩ ⟨E.aW i, 16⟩ := (hE.dW i hi).symm.sub_left (dD i hi)
  have sDW : Mem.Sep (E.aD i) 16 (E.aW i) 16 := dDW.sep (Region.contains_self _ _) (Region.contains_self _ _)
  -- What the loop reads, as it was before it.
  have fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ r' ∈ [(⟨E.A, 16 * i⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Region.sub_prefix (by omega))
  have bS : blockAt t.mem (E.aS i) = blockAt E.m (E.aS i) := blockAt_frame hI.frame fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS i hi i (Nat.le_refl _)
  have bK : blockAt t.mem (E.aK i) = blockAt E.m (E.aK i) := blockAt_frame hI.frame (fA _ (hE.dK i hi))
  have rW : t.mem.readW (E.aW i) 128 = E.T i :=
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dW i hi)) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (remBody_ok E.src t hI.m0 (by rw [eS, hI.rd, hI.wr]; exact hE.inS i hi)
    (by rw [eK, hI.rd, hI.wr]; exact hE.inK i hi) (by rw [eD, hI.wr]; exact hE.inD i hi)
    (by rw [eW, hI.rd, hI.wr]; exact hE.inW i hi) (by rw [eD, eW]; exact sDW))
    fun t₁ ⟨m₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD, eS, eK] at m₁
  rw [eS, eK, eW] at p₁
  have hX : XBinOp.eval .pshufb (t.mem.readW (E.aS i) 128 ^^^ t.mem.readW (E.aK i) 128) revMask = E.X i := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK]
  refine WP.mono (remNext_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  have m' : t'.mem = t.mem.writeW (E.aD i) (t.mem.readW (E.aS i) 128 ^^^ t.mem.readW (E.aK i) 128) := by
    rw [mm, m₁]
  refine ⟨by omega, a10, by rw [a9, show E.r - i - 1 = E.r - (i + 1) by omega],
    fun q h9 h10 => by rw [gg q h9 h10, g₁]; exact hI.gpr q h9 h10, by rw [rd', rd₁, hI.rd],
    by rw [wr', wr₁, hI.wr], ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
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
  · have e : prod (t'.proj 0) = prod (t₁.proj 0) := by simp only [prod, State.proj_xmm, ln]
    rw [e, p₁, hI.prod, hX, rW, hI.y]
    simp only [accR]
    rw [BitVec.xor_comm]
  · rw [ln, y₁]; simp only [Nat.add_one_ne_zero, ↓reduceIte]
  · rw [ln, k₁ _ (by decide)]; exact hI.m0
  · rw [ln, k₁ _ (by decide)]; exact hI.m1

/-- All `r` blocks. -/
theorem remLoop_ok {E : REnv} (hE : E.Ok) {t : State} (hI : RInv E 0 t) :
    WP isa (.loop (.block (remBody E.src ++ remNext)) .ne) t (RInv E E.r) := by
  have r1 := hE.r1
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r - i ∧ i < E.r ∧ RInv E i s) ?_ E.r t ⟨0, rfl, r1, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStep_ok hE hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r - i = 1
  · refine .inl ⟨by simp only [eval, hz, h1, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rwa [show E.r = i + 1 by omega]
  · exact .inr ⟨by simp only [eval, hz, h1, decide_false, Option.map_some, Bool.not_false],
      E.r - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩

end VG.Proof.Gcm.X86_64.StitchZH
