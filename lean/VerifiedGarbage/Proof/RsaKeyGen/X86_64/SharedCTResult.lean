module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRanges

/-! # Reuse the existing result routine's constant-time proof -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The result routine needs the final context and three public header
words. Its existential starting memory can be the final memory: it does
not use the history of the loop's workspace or private stack writes. -/
private theorem result_context {a : SharedLPub} {s : State} (h : SharedLoopEnd a s) :
    LoopEnd a.toLPub s := by
  obtain ⟨hk, hd, mi, c, r, s₀, res, ⟨hctx, h0, h1, hf, hkeep⟩, hS, hrl, ho, hu, hl, hw, henv⟩ := h
  obtain ⟨bm, hc⟩ := hctx
  have hh {k : Nat} (h32 : k < 32)
      (hdj : ∀ r ∈ sharedRoundRanges a.p.w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) :
      word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) :=
    SharedFrame.word hf henv hdj (by
      have := hdr_lt_slot a.p.w 28 h32
      have := a.z28
      omega_arith) hc.good.scr.nowrap
  let u : State := { s₀ with mem := s.mem }
  refine ⟨hk, hd, mi, c, r, u, res, ⟨⟨bm, hc⟩, h0, h1, Frm.refl _ _ _, hkeep⟩,
    hS, hrl, ?_, ?_, ?_, hw⟩
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans ho
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hu
  · exact (hh (by decide) (sharedRoundRanges_hdr _ (by simp))).trans hl

theorem sharedResult_ct : RelCT isa (Two SharedLoopEnd) mrResult fun _ _ => True :=
  two_map SharedLPub.toLPub (fun _ _ h => result_context h) mrResult_ct

end VG.Proof.RsaKeyGen.X86_64
