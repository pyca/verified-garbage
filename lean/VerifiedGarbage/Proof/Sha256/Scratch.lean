module

public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-256's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`reprFrom_congr`) and the data (`Stream.bytesAt_congr`).
-/

@[expose] public section

namespace VG.Proof.Sha256

open VG.Spec.Sha256

/-- `ReprFrom` only depends on the 96 bytes of the state. -/
theorem reprFrom_congr {iv : HashValue} {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 96, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : ReprFrom iv mem p m) : ReprFrom iv mem' p m := by
  refine ⟨by rw [Stream.stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply Stream.bytesAt_congr
  intro i hi
  have := h (32 + i) (by omega)
  rwa [show p + 32 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (32 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

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
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
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
  exact h iv msg (reprFrom_congr (fun i hi => (hs i hi).symm) hr) hc

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
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro iv msg hr hc
  exact h iv msg (reprFrom_congr (fun i hi => (hs i hi).symm) hr) hc

end VG.Proof.Sha256
