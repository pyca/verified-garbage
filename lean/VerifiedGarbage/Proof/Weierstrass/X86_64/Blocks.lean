import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# Short Weierstrass curves on x86-64: code as a sequence of blocks

`blocks ls` runs as the block `ls.flatten` (`blocks_wp`), so `fprogB` (a block
per field operation) runs as `fprog` for a modulus whose products are not
calls (`fprogB_wp`), and `fprog_ok` holds for it.
-/

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

theorem bits_inline (src dst nbytes : Nat) : (bits src dst nbytes).inline = bits src dst nbytes := rfl

/-- Products of fewer than nine words are never calls. -/
theorem callOf_of_ne {M : Mod} (h : M.n ≠ 9) : Mont.callOf M = none := by
  unfold Mont.callOf; exact ite_eq_right_iff.mpr fun h' => absurd h'.1 h

theorem opProg_of_none {M : Mod} (h : Mont.callOf M = none) (op : FOp) : opProg M op = .block (opCode M op) := by
  cases op <;> simp [opProg, opCall?, h]

theorem fprogB_wp {M : Mod} (h : Mont.callOf M = none) :
    ∀ (ops : List FOp) {s : State} {Q : State → Prop},
      WP isa (fprogB M ops).inline s Q ↔ WP isa (.block (fprog M ops)) s Q
  | [], _, _ => by simp [fprogB, progs, fprog, Code.inline]
  | [op], _, _ => by simp [fprogB, progs, fprog, opProg_of_none h, Code.inline]
  | op :: op' :: ops, s, Q => by
    show WP isa (Code.seq (opProg M op).inline (fprogB M (op' :: ops)).inline) s Q ↔ _
    rw [WP.seq_iff, fprog, List.flatMap_cons, WP.block_append_iff, opProg_of_none h]
    exact ⟨fun h' => WP.mono h' fun _ h'' => (fprogB_wp h (op' :: ops)).mp h'',
      fun h' => WP.mono h' fun _ h'' => (fprogB_wp h (op' :: ops)).mpr h''⟩

end VG.Proof.Weierstrass.X86_64
