module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract

/-! Complete candidate and generator-exponent arithmetic has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure CandidatePublic where
  B : Addr
  Z : Nat
  w : Nat
  xp : Addr
  qp : Addr
  xb : List Byte
  qb : List Byte

def CandidatePublic.xLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.xp, p.xb⟩
def CandidatePublic.qLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.qp, p.qb⟩
def CandidatePublic.workspace (p : CandidatePublic) : ArithmeticPublic := ⟨p.B, p.Z, p.w⟩

def CandidateInput (p : CandidatePublic) (s : State) : Prop :=
  LoadState 16 17 p.xLoad s ∧ LoadState 18 19 p.qLoad s

def CandidateFirst (p : CandidatePublic) (s : State) : Prop := LoadState 18 19 p.qLoad s

theorem candidateFirst_state {p : CandidatePublic} {s : State} (h : CandidateInput p s) :
    WP isa (seqs (loadA 0 16 17)) s (CandidateFirst p) := by
  refine WP.mono (loadCandidateArray_ok h.1.ws (by decide) (by decide) (by decide)
    h.1.pointer h.1.length h.1.source h.1.positive h.1.fits) fun t ⟨ht, _, hf, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply hf.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, VG.Impl.Bignum.hdrBytes]; omega
    · have := h.1.ws.h256; have := h.1.ws.scr.nowrap; omega
  refine ⟨ht, (hdr 144 (by decide)).trans h.2.pointer, (hdr 152 (by decide)).trans h.2.length,
    h.2.source.congrK ?_ hk, h.2.positive, h.2.fits⟩
  intro a ha
  apply hf a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.1.ws.sl (by decide : 0 < 16)) ha

theorem candidateSecond_state {p : CandidatePublic} {s : State} (h : CandidateFirst p s) :
    WP isa (seqs (loadA 2 18 19)) s (ArithmeticGood p.workspace) :=
  WP.mono (loadCandidateArray_ok h.ws (by decide) (by decide) (by decide)
    h.pointer h.length h.source h.positive h.fits) (fun _ ⟨ht, _, _, _⟩ => ht)

theorem candidateArithmetic_ct : RelCT isa (Two CandidateInput)
    Impl.Dsa.AArch64.Generation.candidateArithmetic (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.candidateArithmetic
  refine RelCT.seq (two_post
    (two_map CandidatePublic.xLoad (fun _ _ h => h.1)
      (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateFirst_state h)) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.qLoad (fun _ _ h => h)
      (loadCandidate_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => candidateSecond_state h)) ?_
  exact two_map CandidatePublic.workspace (fun _ _ h => h)
    ((RelCT.seq (doubleArray_ct (Or.inr rfl)) (RelCT.seq reduceCandidate_ct (doubleArray_ct (Or.inl rfl)))).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro))

end VG.Proof.Dsa.AArch64.Generation
