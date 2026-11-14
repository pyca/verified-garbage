module

public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on x86-64, without secret residue

The postconditions of `vg_x25519_base` and `vg_x25519_exchange` read the
memory on return only within `out` (`X86_64.Scrub.PostOut`), whatever tables
of constants the code takes: each implementation returns with its whole
stack wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-- The 32 bytes at `o` read the memory only within `⟨o, n⟩`, for `32 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 32 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X25519.bytesAt m₂ o 32 = Spec.X25519.bytesAt m₁ o 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts cs) stack) (Spec.X25519.x25519BaseSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.x25519BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

theorem exchangeOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.exchangeContract (X86_64.abi.withConsts cs) stack) (Spec.X25519.exchangeSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _ ∧ _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

end VG.Proof.X25519.X86_64.Scrub
