module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Bignum.AArch64.Core

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

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
