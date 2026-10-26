module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Calls
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`'s chaining loop

`chainLoop_wp`: each of the `nb` runs of `chainBody` XORs the next block of
the data at `P` into the buffer (`bufOff` in the working space at `W`) and
enciphers it, so that the buffer ends as the chain of those blocks from its
first value.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

/-- The block function's output, as bytes. -/
theorem enc_bytes {m m' : Mem} {a : Addr} {K : Spec.TripleDes.Schedule}
    (h : Spec.TripleDes.blockAt m' a = Spec.TripleDes.encryptBlock K (Spec.TripleDes.blockAt m a)) :
    Spec.Aes.bytesAt m' a 8 = Spec.Cmac.tdesWith K (Spec.Aes.bytesAt m a 8) := by
  rw [VG.Proof.TripleDes.bytesAt_eq, h, ← VG.Proof.TripleDes.ofFn_bytesAt]; rfl

theorem blocksAt_succ8 (m : Mem) (p : Addr) (j : Nat) :
    Spec.Cmac.blocksAt m p 8 (j + 1) =
      Spec.Cmac.blocksAt m p 8 j ++ [Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (8 * j)) 8] := by
  simp [Spec.Cmac.blocksAt, List.range_succ]

/-- After `j` of the `nb` blocks, from the state `c` before the loop. -/
structure LoopInv (c : State) (S W P : Addr) (nb j : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = S
  r4 : t.gpr .r4 = W + BitVec.ofNat 64 512
  r5 : t.gpr .r5 = W
  r29 : t.gpr .r29 = P + BitVec.ofNat 64 (8 * j)
  r30 : t.gpr .r30 = BitVec.ofNat 64 (nb - j)
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = c.gpr r
  rd : t.rd = c.rd
  wr : t.wr = c.wr
  frame : Frame [⟨W, 520⟩] c.mem t.mem
  buf : Spec.Aes.bytesAt t.mem (W + BitVec.ofNat 64 512) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt c.mem S))
      (Spec.Aes.bytesAt c.mem (W + BitVec.ofNat 64 512) 8) (Spec.Cmac.blocksAt c.mem P 8 j)

/-- What the loop needs of the state before it. -/
structure LoopEnv (c : State) (S W P : Addr) (nb : Nat) : Prop where
  key : InRegions (c.rd ++ c.wr) S 384
  scr : ∃ L, 640 ≤ L ∧ (⟨W, L⟩ : Region) ∈ c.wr
  keyScr : Region.Disjoint ⟨S, 384⟩ ⟨W, 640⟩
  scrFit : W.toNat + 640 ≤ 2 ^ 64
  data : ∀ j < nb, InRegions (c.rd ++ c.wr) (P + BitVec.ofNat 64 (8 * j)) 8
  dataScr : ∀ j < nb, Region.Disjoint ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ ⟨W, 520⟩
  nbLt : nb < 2 ^ 64

theorem body_step {c t : State} {S W P : Addr} {nb j : Nat} (he : LoopEnv c S W P nb) (hj : j < nb)
    (hI : LoopInv c S W P nb j t) : WP isa chainBody t (LoopInv c S W P nb (j + 1)) := by
  obtain ⟨L, hL, hW⟩ := he.scr
  have hWt : (⟨W, L⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact hW
  have bufIn : (⟨W, L⟩ : Region).Contains (W + BitVec.ofNat 64 512) 8 :=
    VG.Offset.contains_base _ (show 512 + 8 ≤ L by omega) (by omega)
  have buf520 : (⟨W, 520⟩ : Region).Contains (W + BitVec.ofNat 64 512) (64 / 8) :=
    VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 520 by decide) (by omega)
  unfold chainBody
  refine WP.seq ?_
  refine wp_ld (a := W + BitVec.ofNat 64 512) (by decide) (by decide) (by rw [hI.r5]; rfl)
    (by rw [hI.rd, hI.wr]; exact ⟨_, List.mem_append_right _ hW, bufIn⟩) fun t₁ u₁ => ?_
  refine wp_ld (a := P + BitVec.ofNat 64 (8 * j)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hI.r29]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr, hI.rd, hI.wr]; exact he.data j hj) fun t₂ u₂ => wp_xor fun t₃ u₃ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.r5]; rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact ⟨_, hWt, bufIn⟩) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_subi (by decide) (by decide) fun t₆ u₆ =>
    wp_nil (Q := fun t₆ => WP isa encCall t₆ _) ?_
  have g₄ : ∀ r, r ≠ .r7 → r ≠ .r9 → t₄.gpr r = t.gpr r := fun r h7 h9 => by
    rw [u₄.gpr, u₃.other r h7, u₂.other r h9, u₁.other r h7]
  have g₆ : ∀ r, r ≠ .r7 → r ≠ .r9 → r ≠ .r29 → r ≠ .r30 → t₆.gpr r = t.gpr r := fun r h7 h9 h29 h30 => by
    rw [u₆.other r h30, u₅.other r h29, g₄ r h7 h9]
  have m₆ : t₆.mem = t.mem.writeW (W + BitVec.ofNat 64 512)
      (t.mem.readW (W + BitVec.ofNat 64 512) 64 ^^^ t.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  have rd₆ : t₆.rd = c.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  have wr₆ : t₆.wr = c.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  have F₆ : Frame [⟨W, 520⟩] c.mem t₆.mem := by
    rw [m₆]; exact hI.frame.writeW List.mem_cons_self _ buf520
  -- The state's schedule and the data are outside what the loop writes.
  have hKW : ∀ r ∈ [(⟨W, 520⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact he.keyScr.sub_right (Region.sub_prefix (by decide))
  refine encCall_wp (S := S) (B := W) (L := L) (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r3])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r4])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hI.r5])
    (by rw [rd₆, wr₆]; exact he.key) (by rw [wr₆]; exact hW) hL he.keyScr
    fun v rdv wrv cv v3 v4 v5 fv outv => ?_
  refine ⟨v3, v4, v5, ?_, ?_, fun r hr h29 h30 => ?_, by rw [rdv, rd₆], by rw [wrv, wr₆], F₆.trans fv, ?_⟩
  · rw [cv _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, VG.Offset.add_add, show 8 * j + 8 = 8 * (j + 1) by omega]
  · rw [cv _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := he.nbLt
    omega
  · obtain ⟨-, -, -, -, -, h7, -, h9, -, -, -⟩ := preserved_ne r hr
    rw [cv r hr, g₆ r h7 h9 h29 h30, hI.regs r hr h29 h30]
  · have hdata : Spec.Aes.bytesAt t.mem (P + BitVec.ofNat 64 (8 * j)) 8 =
        Spec.Aes.bytesAt c.mem (P + BitVec.ofNat 64 (8 * j)) 8 :=
      List.map_congr_left fun i hi => hI.frame.bytes (R := ⟨P + BitVec.ofNat 64 (8 * j), 8⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact he.dataScr j hj) (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rw [enc_bytes outv, Proof.TripleDes.scheduleAt_eq_of_frame _ F₆ hKW, m₆, ← Proof.Cmac.le8_readW,
      Mem.readW_writeW_self64, Proof.Cmac.le8_xor, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, hI.buf, hdata,
      blocksAt_succ8, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

theorem chainLoop_wp {c : State} {S W P : Addr} {nb : Nat} (he : LoopEnv c S W P nb)
    {Q : State → Prop} (h0 : LoopInv c S W P nb 0 c) (k : ∀ t, LoopInv c S W P nb nb t → Q t) :
    WP isa chainLoop c Q := by
  unfold chainLoop
  by_cases hz : nb = 0
  · subst hz
    exact WP.ite true (by rw [eval_zero_ofNat c .r30 (by decide) h0.r30]; rfl) (fun _ => wp_nil (k c h0))
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat c .r30 he.nbLt h0.r30]; simp [hz]) (fun h => by cases h)
    fun _ => ?_
  refine WP.loop (M := isa) (Q := Q)
    (fun (m : Nat) (t : State) => ∃ j, m = nb - j ∧ j < nb ∧ LoopInv c S W P nb j t) ?_ nb c
    ⟨0, by omega, by omega, h0⟩
  rintro _ t ⟨j, rfl, hj, hI⟩
  refine WP.mono (body_step he hj hI) fun t' h' => ?_
  have e := eval_nonzero_ofNat' t' .r30 (k := nb - (j + 1)) (by have := he.nbLt; omega) h'.r30
  by_cases hf : j + 1 = nb
  · left; exact ⟨by rw [e]; simp [hf], k t' (hf ▸ h')⟩
  · right; exact ⟨by rw [e]; simp; omega, nb - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE
