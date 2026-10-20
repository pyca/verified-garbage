module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBodyD
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The loop over the blocks after the last group, one at a time, decrypted

`remLoopD1_ok`: `RemLoopOne`'s loop with `StitchZH.remBodyD`, over the `r`
blocks at `S` (read through `src`), their keystream at `P + 768` and their
powers at `W`: writes their decryption to `A` (`REnv.X`) and leaves in the
lower lanes of `xmm8` … `xmm10` the products of each block as read
(`REnv.H`, `Y` added to the first) with its power (`accR`), as `RInvD`
says after each block.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZH (remBodyD remNext)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

/-- Block `j`, as read: what decryption hashes. -/
abbrev REnv.H (E : REnv) (j : Nat) : Block := blockAt E.m (E.aS j)

/-- After `i` of the `r` blocks. -/
structure RInvD (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = accR E.H E.T E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  m0 : t.lane .xmm0 0 = revMask
  m1 : t.lane .xmm1 0 = poly

/-- One block. -/
theorem remStepD_ok {E : REnv} (hE : E.Ok) {i : Nat} (hi : i < E.r) {t : State} (hI : RInvD E i t) :
    WP isa (.block (remBodyD E.src ++ remNext)) t fun t' =>
      RInvD E (i + 1) t' ∧ t'.zf = some (decide (E.r - i = 1)) := by
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
  refine WP.mono (remBodyD_ok E.src t hI.m0 (by rw [eS, hI.rd, hI.wr]; exact hE.inS i hi)
    (by rw [eK, hI.rd, hI.wr]; exact hE.inK i hi) (by rw [eD, hI.wr]; exact hE.inD i hi)
    (by rw [eW, hI.rd, hI.wr]; exact hE.inW i hi) (by rw [eD, eW]; exact sDW))
    fun t₁ ⟨m₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD, eS, eK] at m₁
  rw [eS, eW] at p₁
  have hX : XBinOp.eval .pshufb (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aS i) 128) revMask = E.X i := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK, BitVec.xor_comm]
  have hH : XBinOp.eval .pshufb (t.mem.readW (E.aS i) 128) revMask = E.H i := by
    rw [← blockAt_eq, bS]
  refine WP.mono (remNext_ok t₁ (m := E.r - i) (i := i) (by omega) (by omega) (by rw [g₁, hI.r9])
    (by rw [g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  have m' : t'.mem = t.mem.writeW (E.aD i) (t.mem.readW (E.aK i) 128 ^^^ t.mem.readW (E.aS i) 128) := by
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
theorem remLoopD1_ok {E : REnv} (hE : E.Ok) {t : State} (hI : RInvD E 0 t) :
    WP isa (.loop (.block (remBodyD E.src ++ remNext)) .ne) t (RInvD E E.r) := by
  have r1 := hE.r1
  refine WP.loop (M := isa) (fun n s => ∃ i, n = E.r - i ∧ i < E.r ∧ RInvD E i s) ?_ E.r t ⟨0, rfl, r1, hI⟩
  rintro n s ⟨i, rfl, hi, hIs⟩
  refine WP.mono (remStepD_ok hE hi hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r - i = 1
  · refine .inl ⟨by simp only [eval, hz, h1, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rwa [show E.r = i + 1 by omega]
  · exact .inr ⟨by simp only [eval, hz, h1, decide_false, Option.map_some, Bool.not_false],
      E.r - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩

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
