module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem roundsProg_ok {n : Nat} (hn : n ≤ 24) {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) : WP isa (Impl.Sha3.AArch64.Neon.Pair.roundsProg n) s fun t =>
      CoreKeep s t ∧ Pairs t ((List.range n).foldl Spec.Sha3.rnd A) ((List.range n).foldl Spec.Sha3.rnd B) := by
  induction n generalizing s A B with
  | zero => exact WP.block_nil_iff.mpr ⟨CoreKeep.refl _,hp⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_using [hn]) hp) fun u ⟨hu,hpu⟩ => ?_)
    refine WP.mono (Hw.round2_ok hpu (by omega_using [hn])) fun t ⟨ht,hpt⟩ => ⟨hu.trans ht,?_⟩
    simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpt

end VG.Proof.Sha3.AArch64.Neon
