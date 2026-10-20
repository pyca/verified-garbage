module

public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# HMAC's `init` for a key of any length: its postcondition reads the states alone

`init` for a key of any length (`VG.Spec.Hmac.initAnyKeyContract`) keeps its
working space in a frame of its own, which it wipes before returning
(`Verified.stackScratchWiped`). That needs its postcondition to read the
memory on return only within the function's buffers: the two streaming
states, through the hash function's `Repr` (`initPostOut_local`, for a hash
function whose `Repr` depends only on its state's bytes: `ReprLocal`).
-/

@[expose] public section

namespace VG.Proof.Hmac

open VG.Spec.Hmac

variable (S : StreamingHash) (pb : Nat)

theorem initPostOut_local (hR : ReprLocal S) (hS : S.stateBytes < 2 ^ 64) : ∀ vs m m₁ m₂ r,
    vs.length = ((initSig S).words pb).length →
    (∀ b ∈ Sig.bufs (initSig S).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((initSig S).words pb) (initPost S pb) vs m m₁ r →
      Curry.apply ((initSig S).words pb) (initPost S pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨inn, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs : ∀ (p : Addr), (∀ a, Region.Contains ⟨p, S.stateBytes⟩ a 1 → m₁ a = m₂ a) →
      ∀ i < S.stateBytes, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) :=
    fun p hp i hi => (hp _ (Offset.contains_base _ (by omega) (by omega))).symm
  exact ⟨hR (hs _ hb.1) h.1, hR (hs _ hb.2.1) h.2⟩

end VG.Proof.Hmac
