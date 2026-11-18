module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5's key expansion on AArch64, without secret residue

The postcondition of `vg_cast5_expand_key` reads the memory on return only
within `schedule` (`ScrubAll.ScrubAllOk`, as x86-64's
`Proof/Cast5/X86_64/Scrub.lean` proves it): the code, which has no frames,
returns with every register it may leave secret cleared (`scrubAll 0`,
`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem expandKeyOk :
    ScrubAllOk (Spec.Cast5.expandKeyContract abi) 0 (Spec.Cast5.expandKeySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Cast5.expandKeySig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, sch, _], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [Proof.Cast5.scheduleAt_congr (agree_of hb.2.1 (by decide))]
      exact h

end VG.Proof.Cast5.AArch64.Scrub
