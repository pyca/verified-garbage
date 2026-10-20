module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT

/-! # Candidate shaping preserves the streaming hash's public access pattern -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

theorem qCandidate_ct {H : Hash} (K : HashOK H) (len : Nat) :
    RelCT isa (Two (HashAt K len)) (qCandidate H len) (fun _ _ => True) := by
  unfold qCandidate
  refine RelCT.seq (two_post (Ψ := HashAt K len) (seedHash_ct K len) ?_) ?_
  · intro p s R
    refine WP.mono (seedHash_ok K len R.resources R.esi R.edi R.ebp) fun t ⟨_, _, Kt⟩ => ?_
    exact R.keep Kt (by decide) (by decide) (by decide) (by decide)
  · refine (shape_ct len).mono ?_ (fun _ _ h => h)
    rintro s t ⟨p, hs, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.edi.trans ht.edi.symm
end VG.Proof.Dsa.X86.Generation
