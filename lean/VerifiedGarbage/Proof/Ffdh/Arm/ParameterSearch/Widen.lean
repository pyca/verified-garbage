module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Arm.Inline

/-! The search runs without permission to overwrite its saved registers; widening restores caller permissions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem SearchBuffers.withRegions {p : SearchParams} {s : State} {rd wr : List Region}
    (h : SearchBuffers p s) (reads : Covers (s.rd ++ s.wr) (rd ++ wr))
    (writes : ∀ r ∈ s.wr, r ∈ wr) : SearchBuffers p (s.withRegions rd wr) :=
  ⟨⟨⟨h.controller.space.1, writes _ h.controller.space.2⟩, h.controller.ptr⟩,
    ⟨h.output.1, writes _ h.output.2⟩, ⟨h.used.1, writes _ h.used.2⟩,
    ⟨h.scratch.1, writes _ h.scratch.2⟩, reads _ _ h.tapeRead, h.tapeBytes,
    reads _ _ h.stack, h.below, h.stackSeparate⟩

theorem SearchDone.withRegions {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {rd wr : List Region} (h : SearchDone p result s)
    (reads : Covers (s.rd ++ s.wr) (rd ++ wr)) (writes : ∀ r ∈ s.wr, r ∈ wr) :
    SearchDone p result (s.withRegions rd wr) :=
  ⟨h.buffers.withRegions reads writes, h.usedBound, h.usedPtr, h.used, h.status, h.policy, h.output⟩

theorem SearchStart.withRegions {p : SearchParams} {s : State} {rd wr : List Region}
    (h : SearchStart p s) (reads : Covers (s.rd ++ s.wr) (rd ++ wr))
    (writes : ∀ r ∈ s.wr, r ∈ wr) : SearchStart p (s.withRegions rd wr) := by
  refine ⟨h.storage.withRegions reads writes, ⟨?_, h.incoming.separate⟩,
    h.out, h.used, h.bits, h.counter, h.width, h.entropy⟩
  intro i hi
  have old := h.incoming.incoming i hi
  exact ⟨old.fits, reads _ _ old.readable, old.word⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
