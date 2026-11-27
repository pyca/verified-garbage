module

public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# BLAKE2b's and BLAKE2s's `init` postconditions read only their buffers

On every target, as a residue proof's `PostOut` needs of them
(`Proof/Framework/X86_64/Scrub.lean`, `Proof/Framework/RISCV64/Scrub.lean`):
the streaming state (`repr_congr'`). `update`'s and `finalize`'s are in
`Proof/Blake2/Scratch.lean` (`updateBPost_out`, …).
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.Spec.Blake2

/-- `init`'s postcondition (`initBContract`). -/
abbrev initBPost (pb : Nat) : initBSig.Post pb := fun state outlen key keylen m m' _ =>
  Repr b (init b outlen.toNat keylen.toNat) m' state (keyBlock 64 (bytesAt m key keylen.toNat))

theorem initBPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (initBSig.words pb).length →
    (∀ b ∈ Sig.bufs initBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initBSig.words pb) (initBPost pb) vs m m₁ r →
      Curry.apply (initBSig.words pb) (initBPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [initBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hb
  have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
  exact repr_congr' (by decide)
    (fun i hi => hs i (by simp only [bufOff, blockBytes] at hi; omega_arith)) h

/-- `init`'s postcondition (`initSContract`). -/
abbrev initSPost (pb : Nat) : initSSig.Post pb := fun state outlen key keylen m m' _ =>
  Repr s (init s outlen.toNat keylen.toNat) m' state (keyBlock 32 (bytesAt m key keylen.toNat))

theorem initSPost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (initSSig.words pb).length →
    (∀ b ∈ Sig.bufs initSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSSig.words pb) (initSPost pb) vs m m₁ r →
      Curry.apply (initSSig.words pb) (initSPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [initSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hb
  have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_arith) (by omega_arith))).symm
  exact repr_congr' (by decide)
    (fun i hi => hs i (by simp only [bufOff, blockBytes] at hi; omega_arith)) h

end VG.Proof.Blake2
