module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block

/-! # Composing the generator's sequences of stages -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

theorem seqs_cons_iff (c : Prog isa) (cs : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (c :: cs)) s Q ↔ WP isa c s (fun t => WP isa (seqs cs) t Q) := by
  cases cs with
  | nil => simp only [seqs, WP.block_nil_iff (M := isa)]
  | cons d ds => exact WP.seq_iff

theorem seqs_append_iff (cs ds : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (cs ++ ds)) s Q ↔ WP isa (seqs cs) s (fun t => WP isa (seqs ds) t Q) := by
  induction cs generalizing s Q with
  | nil => simp only [List.nil_append, seqs, WP.block_nil_iff (M := isa)]
  | cons c cs ih => simp only [List.cons_append, seqs_cons_iff, ih]

theorem seqs_range_ok (n : Nat) (code : Nat → Prog isa) (P : Nat → State → Prop)
    (step : ∀ j < n, ∀ s, P j s → WP isa (code j) s (P (j + 1)))
    (s : State) (initial : P 0 s) : WP isa (seqs ((List.range n).map code)) s (P n) := by
  induction n generalizing s with
  | zero => exact WP.block_nil initial
  | succ n ih =>
    rw [List.range_succ, List.map_append, seqs_append_iff]
    refine WP.mono (ih (fun j hj => step j (by omega)) s initial) fun t Pt => ?_
    exact step n (by omega) t Pt

end VG.Proof.Dsa.X86.Generation
