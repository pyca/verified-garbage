module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
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
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # Public-address loads for generator range checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure GeneratorLoadPublic where
  modulus : LoadPublic
  candidate : Addr
  bytes : List Byte

def GeneratorLoadPublic.second (p : GeneratorLoadPublic) : LoadPublic :=
  ⟨p.modulus.B, p.modulus.Z, p.modulus.w, p.candidate, p.bytes⟩

def GeneratorLoadBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  LoadState 16 17 p.modulus s ∧ LoadState 18 19 p.second s

theorem generatorFirst_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa (seqs (loadA 0 16 17)) s (LoadState 18 19 p.second) := by
  refine WP.mono (loadCandidateArray_ok h.1.ws (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) h.1.pointer h.1.length h.1.source h.1.positive h.1.fits)
    fun t ⟨ht, _, f, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) :
      word t.mem p.modulus.B d = word s.mem p.modulus.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega
    · have := h.1.ws.h256; have := h.1.ws.scr.nowrap; omega
  refine ⟨ht, (hdr 144 (by decide)).trans h.2.pointer,
    (hdr 152 (by decide)).trans h.2.length, h.2.source.congrK ?_ hk,
    h.2.positive, h.2.fits⟩
  intro a ha
  apply f a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.1.ws.sl (by decide : 0 < 16)) ha

theorem generatorLoadPair_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.X86_64.Generation.generatorLoadPair
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorLoadPair
  refine RelCT.seq (two_post ?_ (fun _ _ h => generatorFirst_ready h)) ?_
  · exact two_map GeneratorLoadPublic.modulus (fun _ _ h => h.1)
      (loadCandidate_ct (by decide : 0 < 16) (by decide : 16 < 32)
        (by decide : 17 < 32) (by taint_decide) (by taint_decide))
  · exact two_map GeneratorLoadPublic.second (fun _ _ h => h)
      (loadCandidate_ct (by decide : 1 < 16) (by decide : 18 < 32)
        (by decide : 19 < 32) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64.Generation
