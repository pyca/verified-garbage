module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Regrouping the round's statically unrolled instruction sequences -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem seqs_append_exec (cs ds : List (Prog isa)) {s t : State} {tr : List Leak}
    (E : Exec isa (seqs (cs ++ ds)) s tr t) :
    Exec isa (.seq (seqs cs) (seqs ds)) s tr t := by
  induction cs generalizing s tr with
  | nil => exact .seq (show Exec isa (.block []) s [] s from .block rfl) E
  | cons c cs ih =>
    cases cs with
    | nil =>
      cases ds with
      | nil => simpa only [seqs, List.append_nil] using (Exec.seq E (show Exec isa (.block []) t [] t from .block rfl))
      | cons d ds => exact E
    | cons d cs =>
      cases E with
      | seq Ec Er =>
        have split := ih Er
        cases split with
        | seq Es Ed => simpa only [seqs, List.append_assoc] using Exec.seq (Exec.seq Ec Es) Ed

theorem seqs_append_relCT {P R Q : State → State → Prop} (cs ds : List (Prog isa))
    (left : RelCT isa P (seqs cs) R) (right : RelCT isa R (seqs ds) Q) :
    RelCT isa P (seqs (cs ++ ds)) Q := by
  intro s t tr ur u z H E G
  exact RelCT.seq left right _ _ _ _ _ _ H (seqs_append_exec cs ds E) (seqs_append_exec cs ds G)

theorem seqs_range_relCT (n : Nat) (code : Nat → Prog isa) (P : Nat → State → State → Prop)
    (step : ∀ j < n, RelCT isa (P j) (code j) (P (j + 1))) :
    RelCT isa (P 0) (seqs ((List.range n).map code)) (P n) := by
  induction n with
  | zero => exact RelCT.block_nil (fun _ _ H => H)
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    exact seqs_append_relCT _ _ (ih (fun j hj => step j (by omega))) (step n (by omega))

end VG.Proof.MillerRabin.X86
