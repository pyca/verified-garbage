module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Tauto
public import VerifiedGarbage.Impl.Weierstrass.X86_64
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-!
# Short Weierstrass curves on x86-64: code as a sequence of blocks

`blocks ls` runs as the block `ls.flatten` (`blocks_wp`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

theorem blocks_wp : ∀ (ls : List (List Instr)) {s : State} {Q : State → Prop},
    WP isa (blocks ls) s Q ↔ WP isa (.block ls.flatten) s Q
  | [], _, _ => by simp [blocks]
  | [b], _, _ => by simp [blocks]
  | b :: c :: bs, s, Q => by
    rw [show blocks (b :: c :: bs) = .seq (.block b) (blocks (c :: bs)) from rfl, WP.seq_iff, List.flatten_cons, WP.block_append_iff]
    exact ⟨fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mp h',
      fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mpr h'⟩

theorem blocks_noCalls : ∀ (ls : List (List Instr)), (blocks ls).noCalls = true
  | [] => rfl
  | [_] => rfl
  | _ :: c :: bs => by
    show (Code.seq (.block _) (blocks (c :: bs))).noCalls = true
    simp only [Code.noCalls, Bool.true_and]; exact blocks_noCalls (c :: bs)

theorem blocks_inline (ls : List (List Instr)) : (blocks ls).inline = blocks ls :=
  Code.inline_of_noCalls (blocks_noCalls ls)

end VG.Proof.Weierstrass.X86_64
