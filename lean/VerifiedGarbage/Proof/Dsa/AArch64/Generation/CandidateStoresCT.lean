module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoreCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoreCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath

/-! # Save p and its exponent with public addressing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

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
    WP isa (seqs (storeA 5 20 17 VG.Impl.Bignum.Public.sMask)) s (StoreState 21 p.eStore) := by
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
    (header (8 * VG.Impl.Bignum.Public.sMask) (by decide)).trans h.2.mask,
    (fun i hi => by rw [hk.wr]; exact h.2.write i hi), h.2.outside⟩

theorem candidateStores_ct : RelCT isa (Two CandidateStoreState)
    Impl.Dsa.AArch64.Generation.candidateStores (fun _ _ => True) := by
  refine RelCT.seq (two_post
    (two_map CandidateOutputs.pStore (fun _ _ h => h.1)
      (storeCandidate_ct (by decide : 5 < 16) (by decide : 20 < 32) (by taint_decide)))
    (fun _ _ h => candidateStoreFirst_state h)) ?_
  exact two_map CandidateOutputs.eStore (fun _ _ h => h)
    (storeCandidate_ct (by decide : 0 < 16) (by decide : 21 < 32) (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation
