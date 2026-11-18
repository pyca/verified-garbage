module

public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.Instances

-- separate module: target-independent, for every target whose `update` runs with a scrub tail

/-!
# SHA-3's `update` reads the memory on return only within its state

The postcondition of `vg_<instance>_update` reads the memory on return only
through `stateAt` of the state, its 200 bytes (`updatePostOut_local`): what a
scrub tail needs of it, which changes the memory only outside the buffers
(`PPC64LE.Scrub.PostOut`). `finalize`, SHAKE's `finalize` and `squeeze` have
theirs in `Proof/Sha3/Instances.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.Instances

open VG.Spec.Sha3

/-- `updatePost` reads the memory on return only within the state. -/
theorem updatePostOut_local (rate pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  refine ⟨fun msg hr hc => ?_, h.2⟩
  show stateAt m₂ st = _
  rw [stateAt_agree hb.1]
  exact h.1 msg hr hc

end VG.Proof.Sha3.Instances
