module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedCTState

/-! # Compose seed argument setup with the complete subgroup-generation phase -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem seedArguments_ct (n qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore n qLen)) (.block (seedArguments qLen)) (Two (SeedPrepared n qLen)) := by
  have pins : Pins (SeedBefore n qLen) [.rsp] := by
    intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  rcases hlen with rfl | rfl
  all_goals exact two_piece [.rsp] pins (by taint_decide) (fun _ _ h => seedArguments_ready h)

theorem seedSubgroup_ct (H : GenerationHashes) (M : Mont) (K : Kernel)
    (n : Nat) (hn : n = 2 ∨ n = 3) (qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore n qLen))
      (.seq (.block (seedArguments qLen)) (subgroup H.sha1 H.sha256 M.mm K.run qLen)) (fun _ _ => True) :=
  RelCT.seq (seedArguments_ct n qLen hlen)
    (two_map SeedPublic.subgroup (fun _ _ h => seedPrepared_subgroup h) (subgroup_ct H M K n hn qLen hlen))

end VG.Proof.Dsa.X86_64.Generation
