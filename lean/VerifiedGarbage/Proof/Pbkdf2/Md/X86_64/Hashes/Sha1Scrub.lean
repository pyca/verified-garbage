module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
import VerifiedGarbage.Proof.Sha1.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-1's streaming and one-shot functions on x86-64, without secret residue

What `StreamFn.scrub` needs of `updFn`, `finFn` and `digFn` beyond their
code: their postconditions read the memory on return only within the
buffers (`X86_64.Scrub.PostOut`). Each variant
(`Proof/Variants/MdHash/X86_64/Sha1*.lean`) scrubs them with the granules
the residue analysis of its own code selects.
-/

@[expose] public section

namespace VG.Proof.Sha1

open VG.Spec.Sha1

/-! The streaming state (`repr_congr`) and the digest (`Stream.bytesAt_congr`)
are bytes of the function's buffers. -/

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
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 84, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro msg hr hc
  exact Stream.repr_congr hs (h msg hr hc)

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
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < 20, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro msg hr hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h msg hr hc)

theorem digestPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (digestSig.words pb).length →
    (∀ b ∈ Sig.bufs digestSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (digestSig.words pb) (digestPost pb) vs m m₁ r →
      Curry.apply (digestSig.words pb) (digestPost pb) vs m m₂ r := by
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
  have ho : ∀ i < 20, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  show bytesAt m₂ ot 20 = _
  rw [Stream.bytesAt_congr ho]
  exact h

end VG.Proof.Sha1

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha1

open VG.X86_64 VG.X86_64.Scrub

theorem updOut (v : Proof.Sha1.X86_64.Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out 64)

theorem finOut (v : Proof.Sha1.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out 64)

theorem digOut (v : Proof.Sha1.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out 64)

end VG.Proof.Pbkdf2.Md.X86_64.Sha1
