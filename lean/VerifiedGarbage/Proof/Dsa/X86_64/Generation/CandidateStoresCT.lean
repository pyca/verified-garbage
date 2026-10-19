module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoreCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoreCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

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
