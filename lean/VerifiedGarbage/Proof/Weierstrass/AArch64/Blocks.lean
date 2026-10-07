import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog

/-!
# Short Weierstrass curves on AArch64: code as a sequence of blocks

`blocks ls` runs as the block `ls.flatten` (`blocks_wp`), so `fprogB` (a block
per field operation) runs as `fprog`, and `fprog_ok`/`rcb_ok` hold for it.
-/

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

theorem opProg_none {M : Mod} (hc : M.call = none) (op : FOp) : opProg M op = .block (opCode M op) := by
  cases op <;> simp [opProg, hc]

theorem fprogB_none {M : Mod} (hc : M.call = none) :
    ∀ ops : List FOp, fprogB M ops = blocks (ops.map (opCode M))
  | [] => rfl
  | [op] => by simp [fprogB, progs, blocks, opProg_none hc]
  | op :: op' :: ops => by
    have := fprogB_none hc (op' :: ops)
    simp only [fprogB, List.map_cons] at this ⊢
    rw [progs, blocks, opProg_none hc, this]
    · simp
    · simp

/-- For a modulus whose products are inline, `fprogB` runs as `fprog`. -/
theorem fprogB_wp (M : Mod) (ops : List FOp) (hc : M.call = none) {s : State} {Q : State → Prop} :
    WP isa (fprogB M ops) s Q ↔ WP isa (.block (fprog M ops)) s Q := by
  rw [fprogB_none hc, blocks_wp, fprog, List.flatMap_def]

end VG.Proof.Weierstrass.AArch64
