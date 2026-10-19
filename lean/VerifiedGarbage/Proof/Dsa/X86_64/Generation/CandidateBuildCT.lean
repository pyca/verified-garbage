module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmeticCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStoresCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # The complete byte-to-byte p-candidate builder has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64

structure CandidateBuildPublic where
  input : CandidatePublic
  p : Addr
  exponent : Addr

def CandidateBuildPublic.outputs (p : CandidateBuildPublic) : CandidateOutputs :=
  ⟨p.input.B, p.input.Z, p.input.w, p.p, p.exponent⟩

def CandidateBuildState (p : CandidateBuildPublic) (s : State) : Prop :=
  CandidateInput p.input s ∧ CandidateStoreState p.outputs s

theorem candidateArithmetic_storeState {p : CandidateBuildPublic} {s : State} (h : CandidateBuildState p s) :
    WP isa Impl.Dsa.X86_64.Generation.candidateArithmetic s (CandidateStoreState p.outputs) := by
  have hw : Ws s p.input.B p.input.Z p.input.w := h.1.x.ws
  refine WP.mono (candidateArithmetic_ok hw h.1.x.pointer h.1.x.length h.1.q.pointer h.1.q.length
    h.1.x.source h.1.q.source h.1.x.positive h.1.x.fits h.1.q.positive h.1.q.fits
    h.1.qPositive h.1.qFits) fun t ⟨ht, _, _, f, hk⟩ => ?_
  have header (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.input.B d = word s.mem p.input.B d := by
    apply f.word_eq
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        left <;> simp only [slot, hdrBytes] <;> omega
    · have := hw.h256; have := hw.scr.nowrap; omega
  exact ⟨⟨ht, (header 160 (by decide)).trans h.2.1.pointer,
    (header 136 (by decide)).trans h.2.1.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.1.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.1.write i hi), h.2.1.outside⟩,
    ⟨ht, (header 168 (by decide)).trans h.2.2.pointer,
    (header 136 (by decide)).trans h.2.2.length,
    (header (8 * Public.sMask) (by decide)).trans h.2.2.mask,
    (fun i hi => by rw [hk.2.2]; exact h.2.2.write i hi), h.2.2.outside⟩⟩

theorem candidateBuild_ct : RelCT isa (Two CandidateBuildState)
    Impl.Dsa.X86_64.Generation.candidateBuild (fun _ _ => True) :=
  RelCT.seq (two_post (two_map CandidateBuildPublic.input (fun _ _ h => h.1) candidateArithmetic_ct)
    (fun _ _ h => candidateArithmetic_storeState h))
    (two_map CandidateBuildPublic.outputs (fun _ _ h => h) candidateStores_ct)

end VG.Proof.Dsa.X86_64.Generation
