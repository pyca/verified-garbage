module

public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-384's, SHA-512's, SHA-512/224's and SHA-512/256's's postconditions read only their buffers

On every target: the postconditions of `init`, `update`, `finalize` and the one-shot `digest` read the memory on return
only within the function's buffers, as a residue proof's `PostOut` needs of
them (`Proof/Framework/X86_64/Scrub.lean`, `Proof/Framework/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.Spec.Sha512

/-! The streaming state (`repr_congr`) and the digest (`Stream.bytesAt_congr`)
are bytes of the function's buffers. -/

/-- `init`'s postcondition, for the initial hash value `iv` (`initContract`). -/
abbrev initPostOf (iv : HashValue) (pb : Nat) : initSig.Post pb := fun state _ m' _ => Repr iv m' state []

theorem initPost_out (iv : HashValue) (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPostOf iv pb) vs m m₁ r →
      Curry.apply (initSig.words pb) (initPostOf iv pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
  exact Stream.repr_congr (fun i hi => (hb _ (Offset.contains_base _
    (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm) h

theorem updatePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs (updateSig).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
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
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  intro iv msg hr hc
  exact Stream.repr_congr hs (h iv msg hr hc)

theorem finalizePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs (finalizeSig).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₁ r →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < 64, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  intro iv msg hr hl hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h iv msg hr hl hc)

theorem finalizeDigestPost_out (iv : HashValue) (D : Nat) (digest : List Byte → List Byte) (pb : Nat)
    (hD : D < 2 ^ 64) : ∀ vs m m₁ m₂ r, vs.length = ((finalizeDigestSig D).words pb).length →
    (∀ b ∈ Sig.bufs ((finalizeDigestSig D)).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((finalizeDigestSig D).words pb) (finalizeDigestPost iv D digest pb) vs m m₁ r →
      Curry.apply ((finalizeDigestSig D).words pb) (finalizeDigestPost iv D digest pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeDigestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < D, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hD, hi]))).symm
  intro msg hr hl hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h msg hr hl hc)

theorem digestPost_out (D : Nat) (digest : List Byte → List Byte) (pb : Nat) (hD : D < 2 ^ 64) : ∀ vs m m₁ m₂ r, vs.length = ((digestSig D).words pb).length →
    (∀ b ∈ Sig.bufs ((digestSig D)).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₁ r →
      Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [digestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < D, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hD, hi]))).symm
  show bytesAt m₂ ot D = _
  rw [Stream.bytesAt_congr ho]
  exact h

end VG.Proof.Sha512
