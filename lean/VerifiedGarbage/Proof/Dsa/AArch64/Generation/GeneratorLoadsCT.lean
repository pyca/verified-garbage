module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Public-address loads for generator range checks -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

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
      left; simp only [slot, VG.Impl.Bignum.hdrBytes]; omega
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
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.AArch64.Generation.generatorLoadPair
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorLoadPair
  refine RelCT.seq (two_post ?_ (fun _ _ h => generatorFirst_ready h)) ?_
  · exact two_map GeneratorLoadPublic.modulus (fun _ _ h => h.1)
      (loadCandidate_ct (by decide : 0 < 16) (by decide : 16 < 32)
        (by decide : 17 < 32) (by taint_decide) (by taint_decide) (by taint_decide))
  · exact two_map GeneratorLoadPublic.second (fun _ _ h => h)
      (loadCandidate_ct (by decide : 1 < 16) (by decide : 18 < 32)
        (by decide : 19 < 32) (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation
