import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# IDEA's postconditions read only the functions' buffers

What a frame around the code needs of the postconditions (`Verified.stackScratch`,
`Verified.stackScratchWiped`): that `invertKeyPost` and `ecbPost` read the
memory on entry only within the functions' buffers (`invertKeyPost_local`,
`ecbPost_local`), and `ecbPost` the memory on return only within the data
(`ecbPostOut_local`).
-/

namespace VG.Proof.Idea

open VG.Spec.Idea

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

private theorem blocksAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    blocksAt m' p n = blocksAt m p n := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => blockAt_congr fun i hi => ?_
  have := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h _ (by omega)

variable (pb : Nat)

/-- `invertKeyPost` reads the memory on entry only within the schedule. -/
theorem invertKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (invertKeySig.words pb).length →
    (∀ b ∈ Sig.bufs invertKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (invertKeySig.words pb) (invertKeyPost pb) vs m₁ m' r →
      Curry.apply (invertKeySig.words pb) (invertKeyPost pb) vs m₂ m' r
  | [_, _], m₁, m₂, m', r, _, hb, h => by
    simp only [invertKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.addr] (invertKeyPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr] (invertKeyPost pb) _ m₂ m' r
    dsimp only [Curry.apply, invertKeyPost, ArgWord.ofRaw] at h ⊢
    rw [scheduleAt_congr hs]
    exact h

/-- `ecbPost` reads the memory on entry only within the schedule and the data. -/
theorem ecbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost pb) vs m₁ m' r →
      Curry.apply (ecbSig.words pb) (ecbPost pb) vs m₂ m' r
  | [_, data, n], m₁, m₂, m', r, _, hb, h => by
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost pb) _ m₂ m' r
    dsimp only [Curry.apply, ecbPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    rw [scheduleAt_congr hs, blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 8 this; omega)]
    exact h

/-- `ecbPost` reads the memory on return only within the data. -/
theorem ecbPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost pb) vs m m₁ r →
      Curry.apply (ecbSig.words pb) (ecbPost pb) vs m m₂ r
  | [_, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost pb) _ m m₂ r
    dsimp only [Curry.apply, ecbPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    rw [blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 8 this; omega)]
    exact h

end VG.Proof.Idea
