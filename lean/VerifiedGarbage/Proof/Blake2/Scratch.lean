import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# BLAKE2's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`repr_congr`) and the data (`bytesAt_congr`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

/-- `Repr` only depends on the state's bytes: the hash state and the buffered
last block. -/
theorem repr_congr' {w : Nat} (hw : 8 ≤ w) {P : Params w} {h0 : HashValue w} {mem mem' : Mem}
    {p : Addr} {d : List Byte}
    (h : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Repr P h0 mem p d) : Repr P h0 mem' p d := by
  refine ⟨by rw [stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have hb : d.length - blockBytes w * compressed w d ≤ blockBytes w := by
    simp only [compressed]
    have := Nat.div_add_mod (d.length - 1) (blockBytes w)
    have := Nat.mod_lt (d.length - 1) (show 0 < blockBytes w by simp only [blockBytes]; omega)
    omega
  have := h (bufOff w + i) (by omega)
  rwa [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem updateBPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateBSig.words pb).length →
    (∀ b ∈ Sig.bufs updateBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateBSig.words pb) (updateBPost pb) vs m₁ m' r →
      Curry.apply (updateBSig.words pb) (updateBPost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hc hl
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth pb).toNat from bytesAt_congr hd]
    exact h h0 d (repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [bufOff, blockBytes] at hi; omega)).symm) hr) hc hl

theorem finalizeBPost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeBSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m₁ m' r →
        Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hl hc
    exact h h0 d (repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [bufOff, blockBytes] at hi; omega)).symm) hr) hl hc

theorem updateSPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSSig.words pb) (updateSPost pb) vs m₁ m' r →
      Curry.apply (updateSSig.words pb) (updateSPost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hc hl
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth pb).toNat from bytesAt_congr hd]
    exact h h0 d (repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [bufOff, blockBytes] at hi; omega)).symm) hr) hc hl

theorem finalizeSPost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m₁ m' r →
        Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hl hc
    exact h h0 d (repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [bufOff, blockBytes] at hi; omega)).symm) hr) hl hc

end VG.Proof.Blake2
