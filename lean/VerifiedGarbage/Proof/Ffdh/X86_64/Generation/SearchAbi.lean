module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCorrect
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSafety
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete native parameter generation preserves the System V ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

private theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hrc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inputControl s) :=
    (h.2.2.2.2.2.1 _ (by simp)).symm
  have hwr := h.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h.1
  have hd := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [inputBuffers, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hro, hru, hrs, hrc]
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_exec (searchCode_mx v) he
    ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.Ffdh.X86_64.Generation
