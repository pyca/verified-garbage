module

public import VerifiedGarbage.Proof.Rsa.X86.RvHalfTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts

/-! # Preparing recovery uses public lengths for every fixed loop -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover

abbrev NumbersState (g : CallGeometry) (s0 s : State) : Prop :=
  KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
    (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s

theorem halving_relCT (g : CallGeometry) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0) (sp : s0.gpr .esp = t0.gpr .esp) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) (halving g.n)
      (fun s t => HI g.toGeo s0 (fun _ => inputValue g s0.mem 0)
        (2 * (product g s0.mem / 2)) (countBits g) (countBits g) s ∧
        HI g.toGeo t0 (fun _ => inputValue g t0.mem 0)
        (2 * (product g t0.mem / 2)) (countBits g) (countBits g) t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  obtain ⟨count, limit⟩ := left.countBounds
  obtain ⟨ae, ad⟩ := inputArguments left
  obtain ⟨be, bd⟩ := inputArguments right
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := ((halfInit_address g.n).trace _ _ _ _ _ _ (ks_address_agree hs ht sp) e1 f1).1
      have cs := wp_result (halfInit_ok hs (by simp) rfl ae ad (by change countBits g < 2 ^ 32; omega)) e1
      have ds := wp_result (halfInit_ok ht (by simp) rfl be bd (by change countBits g < 2 ^ 32; omega)) f1
      obtain ⟨eq2, is, it⟩ := halfLoop_relCT g.toGeo s0 t0
        (fun _ => inputValue g s0.mem 0) (fun _ => inputValue g t0.mem 0)
        (2 * (product g s0.mem / 2)) (2 * (product g t0.mem / 2)) (countBits g)
        count limit _ _ _ _ _ _ ⟨cs, ds⟩ e2 f2
      exact ⟨by rw [eq1, eq2], is, it⟩

theorem prepare_relCT (g : CallGeometry) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0) (sp : s0.gpr .esp = t0.gpr .esp) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t)
      (.seq (halving g.n) (mont g.n)) (fun _ _ => True) := by
  intro s t tr ur sf tf h es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      obtain ⟨eq1, cs, ds⟩ := halving_relCT g s0 t0 left right sp _ _ _ _ _ _ h e1 f1
      have eq2 := ((mont_workspace g.n).trace _ _ _ _ _ _ (ks_agree cs ds) e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

end VG.Proof.Rsa.X86.Recover
