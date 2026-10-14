module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-! # Grouping adjacent DSA phases without changing their code -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem wpAppendSequences : ∀ {a b : List (Prog isa)}, a ≠ [] → b ≠ [] → ∀ {s : State} {Q : State → Prop},
    WP isa (seqs a) s (fun t => WP isa (seqs b) t Q) → WP isa (seqs (a ++ b)) s Q
  | [], _, ha, _, _, _, _ => absurd rfl ha
  | [c], b, _, hb, _, _, h => by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hb
    exact WP.seq h
  | c :: d :: cs, b, _, hb, _, _, h => by
    exact WP.seq (WP.mono (WP.seq_iff.mp h) fun _ ht =>
      wpAppendSequences (List.cons_ne_nil _ _) hb ht)

end VG.Proof.Dsa.AArch64
