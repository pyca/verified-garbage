module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin

/-!
# The selective cleanup (AArch64)

`verifiedScrubbedSel` states `VerifiedScrubbed` of code followed by
`Impl.Scrub.AArch64.scrubSel W ks c`, after the clears (`withClears`), which
zeroes only the 16-byte granules `ks` of the `W` bytes below the stack
pointer: the theorem a registration binds (`verified := …`), as
`verifiedScrubbedAll` (`ScrubProved.lean`) is of `scrubAll`. It pairs
`RTaintG.Verified.scrubSel` and `RTaintG.noResidue_scrubSel`
(`ResidueWin.lean`), and needs the residue analysis of the window
(`rtaintG`) to end in `doneG W r ks` (by `taint_decide_ct`).
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintF VG.AArch64.RTaintG

/-- `c` with its cleanup of only the granules `ks` of the `W` bytes below the
stack pointer (`scrubSel`, after the clears, `withClears`) meets `c`'s
contract in constant time and returns without secret residue, when the
residue analysis of the window (`rtaintG`) ends in `doneG W r ks`: the
theorem about the code that a registration binds, pairing
`Verified.scrubSel` and `noResidue_scrubSel`. -/
theorem verifiedScrubbedSel {c : Prog isa} {k : Contract isa}
    {r W : Nat} {ks : List Nat} {P₀ : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hks : ks.all (fun k => decide (16 * k + 16 ≤ W)) = true) (hk : ScrubOk k W)
    (hP₀ : ∀ s₁ s₂, Outside 0 s₁ s₂ → PAgree W (wbase s₂.sp 0 W) P₀ s₁.mem s₂.mem)
    (h : ∃ hc, ((rtaintG W).check (RTaintB.init, some (0, P₀, [])) c hc).any (doneG W r ks) = true) :
    VerifiedScrubbed target (scrubSel W ks c) k r :=
  ⟨Verified.scrubSel hv hW hks hk, noResidue_scrubSel hv hW hk.sp hP₀ h⟩

end VG.AArch64.Scrub
