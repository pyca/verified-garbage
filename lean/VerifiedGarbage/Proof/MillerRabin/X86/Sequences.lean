module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block

/-! # Composing the statically unrolled round operations -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

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

theorem seqs_pair (a b : Prog isa) (s : State) (Q : State → Prop) :
    WP isa (seqs [a, b]) s Q ↔ WP isa a s (fun t => WP isa b t Q) := WP.seq_iff

end VG.Proof.MillerRabin.X86
