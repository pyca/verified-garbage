module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBodyD
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# The blocks after the last batch of decryption, one at a time

`remLoopD_ok`: the loop of `StitchAvx8.tailD`, over the `r` blocks at `A`
(read and written in place, through `rdx`), their keystream at `P + 768` and
their powers at `W`, decrypts them, and leaves in the lower lanes of `xmm8`
… `xmm10` the products of each block as it was (`Y` added to the first) with
its power (`accR`), as `RInvD` says after each block, with
`StitchZH.remBodyD_ok` (`Cached/RemBodyD.lean`) for its body.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (prod)
open VG.Impl.Gcm.X86_64.StitchZH (remBodyD remNext)
open VG.Proof.Gcm.X86_64.StitchZH (REnv accR remBodyD_ok remNext_ok addr0 addr768)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep' in_rdwr)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- Block `j` as it was, which decryption hashes. -/
abbrev hblk (E : REnv) (j : Nat) : Block := blockAt E.m (E.aS j)

/-- After `i` of the `r` blocks: as `StitchZH.RInv`, but with the products
of the blocks as they were. -/
structure RInvD (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = accR (hblk E) E.T E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  m0 : t.lane .xmm0 0 = revMask
  m1 : t.lane .xmm1 0 = Impl.Gcm.X86_64.Pclmul.poly

/-- One block, read and written in place (`E.S = E.A`). -/
theorem remStepD_ok {E : REnv} (hE : E.Ok) (hSA : E.S = E.A) {i : Nat} (hi : i < E.r) {t : State}
    (hI : RInvD E i t) :
    WP isa (.block (remBodyD .rdx ++ remNext)) t fun t' =>
      RInvD E (i + 1) t' ∧ t'.zf = some (decide (E.r - i = 1)) := by
  have r15 := hE.r15
  have gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide), hE.gA]
  have gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide), hE.gP]
  have gW : t.gpr .rax = E.W := by rw [hI.gpr _ (by decide) (by decide), hE.gW]
  have hSD : E.aS i = E.aD i := by
    rw [show E.aS i = E.S + BitVec.ofNat 64 (16 * i) from rfl, hSA]
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
  refine WP.mono (remBodyD_ok .rdx t hI.m0 (by rw [eD, hI.rd, hI.wr]; exact in_rdwr (hE.inD i hi))
    (by rw [eK, hI.rd, hI.wr]; exact hE.inK i hi) (by rw [eD, hI.wr]; exact hE.inD i hi)
    (by rw [eW, hI.rd, hI.wr]; exact hE.inW i hi) (by rw [eD, eW]; exact sDW))
    fun t₁ ⟨m₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD, eK] at m₁
  rw [eD, eW] at p₁
  have hX : XBinOp.eval .pshufb (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aD i) 128) revMask = E.X i := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, ← hSD, bS, bK, BitVec.xor_comm]
  have hH : XBinOp.eval .pshufb (t.mem.readW (E.aD i) 128) revMask = hblk E i := by
    rw [← blockAt_eq, ← hSD, bS]
  refine WP.mono (remNext_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  have m' : t'.mem = t.mem.writeW (E.aD i) (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aD i) 128) := by
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
    rw [e, p₁, hI.prod, hH, rW, hI.y]
    simp only [accR]
    rw [BitVec.xor_comm]
  · rw [ln, y₁]; simp only [Nat.add_one_ne_zero, ↓reduceIte]
  · rw [ln, k₁ _ (by decide)]; exact hI.m0
  · rw [ln, k₁ _ (by decide)]; exact hI.m1

/-- All `r` blocks. -/
theorem remLoopD_ok {E : REnv} (hE : E.Ok) (hSA : E.S = E.A) {t : State} (hI : RInvD E 0 t) :
    WP isa (.loop (.block (remBodyD .rdx ++ remNext)) .ne) t (RInvD E E.r) := by
  have r1 := hE.r1
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r - i ∧ i < E.r ∧ RInvD E i s) ?_ E.r t ⟨0, rfl, r1, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStepD_ok hE hSA hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r - i = 1
  · refine .inl ⟨by simp only [eval, hz, h1, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rwa [show E.r = i + 1 by omega]
  · exact .inr ⟨by simp only [eval, hz, h1, decide_false, Option.map_some, Bool.not_false],
      E.r - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
