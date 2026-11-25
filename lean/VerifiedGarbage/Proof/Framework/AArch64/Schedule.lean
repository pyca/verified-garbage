module

public import VerifiedGarbage.Impl.AArch64Schedule
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave

/-!
# AArch64: a reordered block runs as the block does

`ok xb ks l` checks, on footprints (`Interleave.lean`), that each instruction
`schedule ks l` takes is independent of those it overtakes.
-/

@[expose] public section

namespace VG.AArch64.Schedule

open VG VG.AArch64.Interleave
open VG.Impl.AArch64Schedule (schedule)

/-- The instruction of footprint `f` is independent of those before place `k`. -/
def free (xb : Reg) (f : Fp) : Nat → List (Option Fp) → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | k + 1, some g :: gs => g.indep xb f && free xb f k gs
  | _ + 1, none :: _ => false

def okF (xb : Reg) : List Nat → List (Option Fp) → Bool
  | [], _ => true
  | k :: ks, gs =>
    match gs[k]? with
    | some (some f) => free xb f k gs && okF xb ks (gs.eraseIdx k)
    | some none => k == 0 && okF xb ks (gs.eraseIdx k)
    | none => true

def ok (xb : Reg) (ks : List Nat) (l : List Instr) : Bool := okF xb ks (l.map (fp xb))

theorem free_indep {xb : Reg} {f : Fp} : ∀ {k : Nat} {l : List Instr}, free xb f k (l.map (fp xb)) = true →
    ∀ x ∈ l.take k, ∃ F, fp xb x = some F ∧ Indep xb F f
  | 0, _, _, x, hx => by simp at hx
  | _ + 1, [], _, x, hx => by simp at hx
  | k + 1, y :: l, h, x, hx => by
    simp only [List.map_cons] at h
    rcases hy : fp xb y with _ | g
    · rw [hy] at h; simp [free] at h
    · rw [hy] at h
      simp only [free, Bool.and_eq_true] at h
      rw [List.take_succ_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨g, hy, Indep.of h.1⟩
      · exact free_indep h.2 x hx

theorem split_at {l : List Instr} {k : Nat} {i : Instr} (h : l[k]? = some i) :
    l = l.take k ++ i :: l.drop (k + 1) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem eraseIdx_eq (l : List Instr) (k : Nat) : l.eraseIdx k = l.take k ++ l.drop (k + 1) :=
  List.eraseIdx_eq_take_drop_succ l k

theorem map_erase {α β : Type} (f : α → β) : ∀ (l : List α) (k : Nat), (l.eraseIdx k).map f = (l.map f).eraseIdx k
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: l, k + 1 => by simp only [List.eraseIdx_cons_succ, List.map_cons, map_erase f l k]

/-- Taking an independent instruction first. -/
theorem run_pull {xb : Reg} {a b : List Instr} {i : Instr} {f : Fp} (hf : fp xb i = some f)
    (ha : ∀ x ∈ a, ∃ F, fp xb x = some F ∧ Indep xb F f) (s : State) :
    runBlock isa (a ++ i :: b) s = runBlock isa (i :: (a ++ b)) s := by
  rw [runBlock_append]
  show _ = (exec i s).bind (runBlock isa (a ++ b))
  have e : runBlock isa (a ++ b) = fun u => (runBlock isa a u).bind (runBlock isa b) := funext (runBlock_append a b)
  rw [e, ← Option.bind_assoc, comm_block (y := i) (fun x hx => by
    obtain ⟨F, h1, h2⟩ := ha x hx; exact ⟨F, f, h1, hf, h2⟩) s, Option.bind_assoc]
  rfl

theorem run_eq {xb : Reg} : ∀ (ks : List Nat) {l : List Instr}, ok xb ks l = true → ∀ s,
    runBlock isa (schedule ks l) s = runBlock isa l s
  | [], _, _, _ => rfl
  | k :: ks, l, h, s => by
    unfold schedule
    rcases hi : l[k]? with _ | i
    · rfl
    simp only [ok, okF, List.getElem?_map, hi, Option.map_some] at h
    have tail : okF xb ks ((l.map (fp xb)).eraseIdx k) = true →
        ∀ u, runBlock isa (schedule ks (l.eraseIdx k)) u = runBlock isa (l.eraseIdx k) u := fun h u =>
      run_eq ks (by rw [ok, map_erase]; exact h) u
    rcases hf : fp xb i with _ | f
    · simp only [hf, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      show (exec i s).bind _ = _
      rw [funext (tail h)]
      cases l with
      | nil => cases hi
      | cons y l => cases hi; rfl
    · simp only [hf, Bool.and_eq_true] at h
      show (exec i s).bind _ = _
      rw [funext (tail h.2), eraseIdx_eq]
      conv => rhs; rw [split_at hi]
      exact (run_pull hf (free_indep h.1) s).symm

end VG.AArch64.Schedule
