module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DispatchCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetupCT

/-! # Entry initialization composes with dispatch and the complete generator -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

def EntryBefore (n : Nat) (p : ParameterPublic) (s : State) : Prop :=
  EntryState p.context s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.randUsed = 0

theorem entryReady_ct (n : Nat) :
    RelCT isa (Two (EntryBefore n)) (.block (entryHeader ++ entryIncoming ++ entryDerived))
      (Two (DispatchBefore n)) := by
  refine two_post (entrySetup_ct.mono ?_ (fun _ _ _ => True.intro)) ?_
  · rintro s t ⟨p, hs, ht⟩
    exact hs.1.rsp.trans ht.1.rsp.symm
  · intro p s ⟨h, hf, hw, hz⟩
    refine WP.mono (entryReady_ok h) fun t ⟨W, ht, h16, _, hk⟩ => ?_
    exact ⟨⟨W, ht, by rw [hz]; exact h16⟩,
      hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, rfl, rfl⟩

theorem entryBody_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (EntryBefore n)) (entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (fun _ _ => True) :=
  RelCT.seq (entryReady_ct n) (dispatch_ct (checkName := checkName) H M Sq T n hn)

end VG.Proof.Dsa.X86_64.Generation
