module

public import VerifiedGarbage.Proof.Rsa.X86.RvSearchTimingState

/-! # Equal declared attempt counts give equal search traces -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover

theorem searchLoop_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) (tcC : 1 ≤ C.V sTc) (tcD : 1 ≤ D.V sTc)
    (tries : C.tries = D.tries) :
    RelCT isa (fun s t => CI g C.s0 C.A C.AW C.V 0 s ∧ CI g D.s0 D.A D.AW D.V 0 t)
      (.loop (candBody g.n) .ne) (fun _ _ => True) := by
  have top := VG.Proof.Rsa.go_le m (C.V sTc) (C.AW wR) 100 (by decide)
  change C.tries ≤ 100 at top
  have low := VG.Proof.Rsa.go_ge1 m (C.V sTc) (C.AW wR) (k := 99) (by decide)
  change 1 ≤ C.tries at low
  have loop := VG.RelCT.loop (M := isa) (body := candBody g.n) (c := .ne)
    (Q := fun _ _ => True)
    (fun remaining s t => ∃ j, j + remaining = 100 ∧ 0 < remaining ∧
      SearchInvariant C j s ∧ SearchInvariant D j t)
    (fun remaining s t tr ur sf tf ⟨j, sum, pos, hs, ht⟩ es et => by
      have hj : j < 100 := by omega
      have trace := (candBody_relCT (C.atCandidate j hj) (D.atCandidate j hj) sp
        _ _ _ _ _ _ ⟨hs.1, ht.1⟩ es et).1
      obtain ⟨cs, cn⟩ := wp_result (searchBody_post C tcC hs) es
      obtain ⟨ds, dn⟩ := wp_result (searchBody_post D tcD ht) et
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · rw [cs, ds, tries]
      · intro more
        have next : j + 1 < C.tries := of_decide_eq_true (Option.some.inj (cs.symm.trans more))
        have moreD : isa.eval .ne tf = some true := ds.trans (by rw [← tries]; exact congrArg some (decide_eq_true next))
        exact ⟨remaining - 1, by omega, j + 1, by omega, by omega, cn more, dn moreD⟩) 100
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, rfl, by decide, ⟨hs, by omega, rfl⟩, ⟨ht, by omega, rfl⟩⟩
  · intro s t h; exact h

end VG.Proof.Rsa.X86.Recover
