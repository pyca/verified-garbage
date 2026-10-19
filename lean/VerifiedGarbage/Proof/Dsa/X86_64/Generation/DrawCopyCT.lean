module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT

/-! # Witness draws reveal their public tape position and widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64

structure DrawPublic where
  prime : PrimeParams
  used : Nat

def DrawBefore (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  (∃ mi, PrimeState p.prime mi p.used s) ∧ p.prime.len = len ∧ p.prime.drawBytes = drawBytes

def DrawCopyReady (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  s.gpr .rsi = off p.prime.rp (p.used + (drawBytes - len)) ∧ s.gpr .rdi = p.prime.p ∧
    s.gpr .rcx = BitVec.ofNat 64 len ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * len)

theorem drawCopy_ct (len drawBytes : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi])
      (.block (Impl.Dsa.X86_64.Generation.drawCopyArgs len drawBytes)) hc).isSome = true) :
    RelCT isa (Two (DrawBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.drawCopy len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.drawCopy
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := DrawCopyReady len drawBytes) (two_taint [.rdi] ?_ ht) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · intro p s h
    obtain ⟨mi, hs⟩ := h.1
    have hlen : len ≤ drawBytes := by rw [← h.2.1, ← h.2.2]; exact p.prime.lenDraw
    have hd : drawBytes ≤ 1024 := by rw [← h.2.2]; exact p.prime.drawMax
    exact WP.mono (drawCopyArgs_ok hs.ready.good p.prime.dims.z hlen hd hs.rand hs.ptr hs.used)
      fun t ⟨_, hsi, hdi, hcx, hdx, _, _⟩ => ⟨hsi, hdi, hcx, hdx⟩
  · exact two_taint [.rdi, .rsi, .rcx, .rdx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.1.trans ht.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
