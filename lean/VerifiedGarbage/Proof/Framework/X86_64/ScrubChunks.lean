module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.Framework.CodeOnce

/-!
# x86-64 residue: wiping the stack in chosen chunks

`chunks r.stack` ends its 16-byte granules at the stack pointer on entry,
which is 8 off 16: every 16-byte store of a wipe in them is unaligned, and
one in four of them splits a cache line. For any chunks `cs` summing to the
stack (a chunk of 8 bytes at the top puts the granules of the chunk below
it 16 bytes aligned, as `chunksA` does), wiping every granule leaves no
residue on the stack (`resOk_allC`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- For any chunks `cs` of the stack: with every granule of the stack
wiped, `ResOk` asks nothing of the code. -/
theorem resOk_allC (c : Prog isa) (k : Contract isa) {stack : Nat} {cs : List Nat}
    (h8 : ∀ b ∈ cs, b % 8 = 0) (hs : cs.sum = stack) : ResOk c k stack (allKs cs) cs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ _ _ _ _ _ _ _ _ x hx hn
  exact absurd (wcov_all h8 (by rw [hs]; exact hx)) hn

end VG.X86_64.RScrub
