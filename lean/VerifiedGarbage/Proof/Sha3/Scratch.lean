import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge with its working space on the stack: locality

`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` keep their
working space in a frame of their own (`Verified.stackScratch`), around code
proved with the working space as an argument (`Spec.Sha3.absorbScratchContract`
and the others, which `vg_keccak_absorb_scratch` and the others are emitted
with).

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the pre- and postconditions to read the memory on entry
only within the function's buffers (`absorbPost_local`, `padPost_local`,
`squeezePost_local`): the data, and the state, through `stateAt`, which
reads only its 200 bytes (`stateAt_congr`).
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

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

variable (pb : Nat)

theorem absorbPre_local : ∀ vs m₁ m₂, vs.length = (absorbSig.words pb).length →
    (∀ b ∈ Sig.bufs absorbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (absorbSig.words pb) (absorbPre pb) vs m₁ →
      Curry.apply (absorbSig.words pb) (absorbPre pb) vs m₂
  | [_, _, _, _, _], _, _, _, _, h => h

theorem absorbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (absorbSig.words pb).length →
    (∀ b ∈ Sig.bufs absorbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (absorbSig.words pb) (absorbPost pb) vs m₁ m' r →
      Curry.apply (absorbSig.words pb) (absorbPost pb) vs m₂ m' r
  | [st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [absorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (absorbPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (absorbPost pb) _ m₂ m' r
    dsimp only [Curry.apply, absorbPost, ArgWord.ofRaw] at h ⊢
    refine ⟨fun msg hr hp => ?_, h.2⟩
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    refine h.1 msg ?_ hp
    unfold Spec.Sha3.Repr at hr ⊢
    rw [← hr]; exact (stateAt_congr fun i hi => hs i (by omega)).symm

theorem padPre_local : ∀ vs m₁ m₂, vs.length = (padSig.words pb).length →
    (∀ b ∈ Sig.bufs padSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (padSig.words pb) (padPre pb) vs m₁ →
      Curry.apply (padSig.words pb) (padPre pb) vs m₂
  | [_, _, _, _], _, _, _, _, h => h

theorem padPost_local : ∀ vs m₁ m₂ m' r, vs.length = (padSig.words pb).length →
    (∀ b ∈ Sig.bufs padSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (padSig.words pb) (padPost pb) vs m₁ m' r →
      Curry.apply (padSig.words pb) (padPost pb) vs m₂ m' r
  | [st, _, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [padSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      Elem.size] at hb
    have hs := agree_of hb
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.int 32]
      (padPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.int 32]
      (padPost pb) _ m₂ m' r
    dsimp only [Curry.apply, padPost, ArgWord.ofRaw] at h ⊢
    intro msg hr hp
    refine h msg ?_ hp
    unfold Spec.Sha3.Repr at hr ⊢
    rw [← hr]; exact (stateAt_congr fun i hi => hs i (by omega)).symm

theorem squeezePre_local : ∀ vs m₁ m₂, vs.length = (squeezeSig.words pb).length →
    (∀ b ∈ Sig.bufs squeezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (squeezeSig.words pb) (squeezePre pb) vs m₁ →
      Curry.apply (squeezeSig.words pb) (squeezePre pb) vs m₂
  | [_, _, _, _, _], _, _, _, _, h => h

theorem squeezePost_local : ∀ vs m₁ m₂ m' r, vs.length = (squeezeSig.words pb).length →
    (∀ b ∈ Sig.bufs squeezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (squeezeSig.words pb) (squeezePost pb) vs m₁ m' r →
      Curry.apply (squeezeSig.words pb) (squeezePost pb) vs m₂ m' r
  | [st, _, _, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [squeezeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (squeezePost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (squeezePost pb) _ m₂ m' r
    dsimp only [Curry.apply, squeezePost, ArgWord.ofRaw] at h ⊢
    rw [stateAt_congr (m := m₁) (m' := m₂) fun i hi => hs i (by omega)]
    exact h

end VG.Proof.Sha3
