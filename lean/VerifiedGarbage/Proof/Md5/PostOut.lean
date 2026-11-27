module

public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# MD5's postconditions read only their buffers

On every target: the postconditions of `init`, `update` and `finalize`
read the memory on return only within the function's buffers, as a residue
proof's `PostOut` needs of them (`Proof/Framework/X86_64/Scrub.lean`,
`Proof/Framework/RISCV64/Scrub.lean`): the streaming state
(`Stream.repr_congr`) and the digest (`Stream.bytesAt_congr`).
-/

@[expose] public section

namespace VG.Proof.Md5

open VG.Spec.Md5

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

/-- `init`'s postcondition (`initContract`). -/
abbrev initPost (pb : Nat) : initSig.Post pb := fun state _ m' _ => Repr m' state []

theorem initPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m m₁ r →
      Curry.apply (initSig.words pb) (initPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
  exact Stream.repr_congr (fun i hi => agreeBuf (n := 80 * Elem.size .u8) (by decide) hb i
    (by simp only [Elem.size]; omega_using [hi])) h

theorem updatePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  intro msg hr hc
  exact Stream.repr_congr (fun i hi => agreeBuf (n := 80 * Elem.size .u8) (by decide) hb.1 i
    (by simp only [Elem.size]; omega_using [hi])) (h msg hr hc)

theorem finalizePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₁ r →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  intro msg hr hc
  show bytesAt m₂ ot 16 = _
  rw [Stream.bytesAt_congr fun i hi => agreeBuf (n := 16 * Elem.size .u8) (by decide) hb.2 i
    (by simp only [Elem.size]; omega_using [hi])]
  exact h msg hr hc

end VG.Proof.Md5
