module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DispatchCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryReady

/-! Initialize public frame arguments and dispatch the complete generator. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64 VG.Impl.Dsa.AArch64.Generation

def EntryBefore (p : ParameterPublic) (s : State) : Prop :=
  EntryState p.context s ∧ p.randUsed = 0

theorem entryReady_ct : RelCT isa (Two EntryBefore)
    (.block (entryHeader ++ entryIncoming ++ entryDerived)) (Two DispatchBefore) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_
  intro p s ⟨h, hz⟩
  exact WP.mono (entryReady_ok h) fun t ⟨W, ht, h16, _, _⟩ =>
    ⟨⟨W, ht, by rw [hz]; exact h16⟩, rfl, rfl⟩

theorem entryCore_ct (H : GenerationHashes) (M : Mont) (K : Kernel) :
    RelCT isa (Two EntryBefore)
      (.seq (.block (entryHeader ++ entryIncoming ++ entryDerived))
        (dispatch H.sha1 H.sha256 M.mm K.run)) (fun _ _ => True) :=
  RelCT.seq entryReady_ct (dispatch_ct H M K)

end VG.Proof.Dsa.AArch64.Generation
