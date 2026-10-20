module

import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.CT
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# SHA-512 with AVX2 on x86-64, rolled: verified

`compress_verified`: `Impl.Sha512.X86_64.Avx2Rolled.compress` against
`Proof.Sha512.compressWideX86_64`, the contract of the unrolled code, under
the plain calling convention: the table of round constants is carried by
the code (`aluTbl`), not given by the contract.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2Rolled

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressWideX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem compress_verified :
    Verified X86_64.target compress Proof.Sha512.compressWideX86_64 := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact compress_ct s₁ s₂ t₁ t₂ s₁' s₂' (pre_of s₁ h₁) (pre_of s₂ h₂) ⟨h1, h2, h3, h4⟩ e₁ e₂
  · refine ⟨Avx2.satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.X86_64.Avx2.Rolled
