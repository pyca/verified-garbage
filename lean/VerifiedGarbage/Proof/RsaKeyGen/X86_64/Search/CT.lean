module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Safety
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Safety
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # The search's timing depends on its public data and its trace

Two runs at the same point (`SearchPoint`) agree on the public descriptor,
the octets consumed, the counted candidates left and the trace still to come,
which each run's own search from there gives. The next candidate's leak is
the trace's next entry, and with it what became of the candidate: its status
and the octets it consumed.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search

structure SearchPoint where
  inputs : SearchPublic
  used : Nat
  remaining : Nat
  trace : List Nat

def SearchCTL (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace

/-- Some loop state with the public descriptor `p`. -/
def SearchAny (p : SearchPublic) (s : State) : Prop :=
  ∃ original used remaining, SearchLive p original used remaining s

theorem SearchCTL.any {q : SearchPoint} {s : State} (h : SearchCTL q s) : SearchAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, h⟩

theorem search_any_pins : Pins SearchAny [.r12, .rsp] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.r12.trans h₂.r12.symm, h₁.rsp.trans h₂.rsp.symm]

theorem search_ctl_pins : Pins SearchCTL [.r12, .rsp] :=
  fun _ _ _ h₁ h₂ => search_any_pins _ _ _ h₁.any h₂.any

/-- The next candidate's leak, from the trace. -/
def SearchPoint.leak (q : SearchPoint) : List Nat := (q.trace.drop 1).take (q.trace.headD 0)

theorem SearchCTL.leak {q : SearchPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    Spec.RsaKeyGen.candidateLeak q.inputs.len q.inputs.eB (searchP original)
      ((searchRand original).drop q.used) = q.leak := by
  obtain ⟨rest, hrest⟩ := VG.Proof.RsaKeyGen.Search.search_trace (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) hr ((searchRand original).drop q.used)
  unfold tailOf at ht
  rw [hrest] at ht
  unfold SearchPoint.leak
  rw [← ht]
  simp [VG.Proof.RsaKeyGen.Search.entry]

end VG.Proof.RsaKeyGen.X86_64.Search
