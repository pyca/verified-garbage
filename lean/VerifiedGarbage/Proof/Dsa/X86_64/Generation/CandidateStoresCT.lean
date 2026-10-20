module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoreCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoreCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Save p and its exponent with public addressing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure CandidateOutputs where
  B : Addr
  Z : Nat
  w : Nat
  p : Addr
  exponent : Addr

def CandidateOutputs.pStore (p : CandidateOutputs) : StorePublic := ⟨p.B, p.Z, p.w, p.p⟩
def CandidateOutputs.eStore (p : CandidateOutputs) : StorePublic := ⟨p.B, p.Z, p.w, p.exponent⟩
def CandidateStoreState (p : CandidateOutputs) (s : State) : Prop :=
  StoreState 20 p.pStore s ∧ StoreState 21 p.eStore s

theorem candidateStoreFirst_state {p : CandidateOutputs} {s : State} (h : CandidateStoreState p s) :
    WP isa (seqs (storeA 5 20 17 Public.sMask)) s (StoreState 21 p.eStore) := by
  refine WP.mono (storeCandidateArray_ok h.1.ws (by decide : 5 < 16) (by decide : 20 < 32)
    h.1.pointer h.1.length h.1.mask h.1.write h.1.outside) fun t ⟨_, _, ht, f, hk⟩ => ?_
  change Frm p.B [(p.Z, 2 ^ 64)] s.mem t.mem at f
  have hw : Ws s p.B p.Z p.w := h.1.ws
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      exact Or.inl (Nat.le_trans hd hw.h256)
    · have := hw.h256; have := hw.scr.nowrap; omega
  exact ⟨ht, (header 168 (by decide)).trans h.2.pointer,
    (header 136 (by decide)).trans h.2.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.write i hi), h.2.outside⟩

theorem candidateStores_ct : RelCT isa (Two CandidateStoreState)
    Impl.Dsa.X86_64.Generation.candidateStores (fun _ _ => True) := by
  refine RelCT.seq (two_post
    (two_map CandidateOutputs.pStore (fun _ _ h => h.1)
      (storeCandidate_ct (by decide : 5 < 16) (by decide : 20 < 32) (by taint_decide)))
    (fun _ _ h => candidateStoreFirst_state h)) ?_
  exact two_map CandidateOutputs.eStore (fun _ _ h => h)
    (storeCandidate_ct (by decide : 0 < 16) (by decide : 21 < 32) (by taint_decide))

end VG.Proof.Dsa.X86_64.Generation
