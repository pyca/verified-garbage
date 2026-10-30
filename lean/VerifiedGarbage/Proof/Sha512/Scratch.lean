module

public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# SHA-512's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`Stream.repr_congr`) and the data (`Stream.bytesAt_congr`).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.Spec.Sha512

theorem updatePost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m₁ m' r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [updateSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_array, Sig.bufs_slice, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
    fun i hi => by
      have := Nat.mod_le ln.toNat (2 ^ pb)
      have := ln.isLt
      rw [BitVec.toNat_setWidth] at hi
      exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro iv msg hr hc
  rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
    bytesAt m₁ dt (ln.setWidth pb).toNat from Stream.bytesAt_congr hd]
  exact h iv msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

theorem finalizePost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₁ m' r →
        Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_array, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro iv msg hr hl hc
  exact h iv msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hl hc

end VG.Proof.Sha512
