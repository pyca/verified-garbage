module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem roundsProg_ok (sha3 : Bool) {n : Nat} (hn : n ≤ 24) {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) : WP isa (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 n) s fun t =>
      CoreKeep s t ∧ Pairs t ((List.range n).foldl Spec.Sha3.rnd A) ((List.range n).foldl Spec.Sha3.rnd B) := by
  induction n generalizing s A B with
  | zero => exact WP.block_nil_iff.mpr ⟨CoreKeep.refl _,hp⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega) hp) fun u ⟨hu,hpu⟩ => ?_)
    have hr : WP isa (.block (if sha3 then Impl.Sha3.AArch64.Sha3.Vector.round n else
        Impl.Sha3.AArch64.Neon.Vector.round n)) u fun t => CoreKeep u t ∧
          Pairs t (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd A) n)
            (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd B) n) := by
      cases sha3
      · exact round_ok hpu (by omega)
      · exact Hw.round2_ok hpu (by omega)
    refine WP.mono hr fun t ⟨ht,hpt⟩ => ⟨hu.trans ht,?_⟩
    simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpt

end VG.Proof.Sha3.AArch64.Neon
