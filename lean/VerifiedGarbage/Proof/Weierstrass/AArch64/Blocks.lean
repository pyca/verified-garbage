module

import VerifiedGarbage.Proof.Weierstrass.AArch64.LadderFieldLit

public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# Short Weierstrass curves on AArch64: code as a sequence of blocks

`blocks ls` runs as the block `ls.flatten` (`blocks_wp`), so `fprogB` (a block
per field operation) runs as `fprog`, and `fprog_ok`/`rcb_ok` hold for it.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass

theorem blocks_wp : ∀ (ls : List (List Instr)) {s : State} {Q : State → Prop},
    WP isa (blocks ls) s Q ↔ WP isa (.block ls.flatten) s Q
  | [], _, _ => by simp [blocks]
  | [b], _, _ => by simp [blocks]
  | b :: c :: bs, s, Q => by
    rw [show blocks (b :: c :: bs) = .seq (.block b) (blocks (c :: bs)) from rfl, WP.seq_iff, List.flatten_cons, WP.block_append_iff]
    exact ⟨fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mp h',
      fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mpr h'⟩

theorem opProg_none {M : Mod} (hc : Mont.callOf M = none) (hm : M.n ≠ 8) (op : FOp) : opProg M op = .block (opCode M op) := by
  have hl : ladderFieldLayout M = false := by
    cases h : ladderFieldLayout M with
    | false => rfl
    | true => exact (hm (congrArg Mod.n (LadderFieldLit.layout_eq h))).elim
  have hs : ladderField? M op = none := by simp only [ladderField?, hl, Bool.false_eq_true, ↓reduceIte]
  cases op <;> simp only [opProg, hs, opProgRaw, hc]

theorem fprogB_none {M : Mod} (hc : Mont.callOf M = none) (hm : M.n ≠ 8) :
    ∀ ops : List FOp, fprogB M ops = blocks (ops.map (opCode M))
  | [] => rfl
  | [op] => by simp [fprogB, progs, blocks, opProg_none hc hm]
  | op :: op' :: ops => by
    have := fprogB_none hc hm (op' :: ops)
    simp only [fprogB, List.map_cons] at this ⊢
    rw [progs, blocks, opProg_none hc hm, this]
    · simp
    · simp

/-- For a modulus whose products are inline, `fprogB` runs as `fprog`. -/
theorem fprogB_wp (M : Mod) (ops : List FOp) (hc : Mont.callOf M = none) (hm : M.n ≠ 8 := by decide) {s : State} {Q : State → Prop} :
    WP isa (fprogB M ops) s Q ↔ WP isa (.block (fprog M ops)) s Q := by
  rw [fprogB_none hc hm, blocks_wp, fprog, List.flatMap_def]

end VG.Proof.Weierstrass.AArch64
