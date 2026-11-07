module

public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.CtrCipher

-- separate module: shared by the final function's proofs of every target.

/-!
# SM4-CTR of a message's last piece: the contract's postcondition, by name

Not trusted, and the same on every target. `ctrFinalPost`:
`Spec.Sm4.ctrFinalContract`'s postcondition (`ctrFinalContract_eq`), which
reads the memory on entry and on return only within the function's buffers
(`ctrFinalPost_local`, `ctrFinalPostOut_local`), as a frame that keeps
working space on the stack needs. What a final function leaves gives `Spec.Ctr.CryptFinal` by
`Proof.Modes.CtrFinal.cryptFinal_of`, for any cipher.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG.Spec.Sm4

/-- `Spec.Sm4.ctrFinalContract`'s postcondition. -/
def ctrFinalPost (pb : Nat) : ctrFinalSig.Post pb := fun schedule ctr data len m m' _ =>
  Spec.Ctr.CryptFinal (cipher (scheduleAt m schedule)) m m' ctr data len.toNat

theorem ctrFinalContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.Sm4.ctrFinalContract A stack =
      ctrFinalSig.contract A (post := ctrFinalPost A.ptrBits) (writeArgs := true) (stack := stack) := rfl

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem agree_of' {m₁ m₂ : Mem} {p : Addr} {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- `ctrFinalPost` reads the memory on return only within the buffers. -/
theorem ctrFinalPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrFinalSig.words pb) (ctrFinalPost pb) vs m m₁ r →
      Curry.apply (ctrFinalSig.words pb) (ctrFinalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [k, ctr, data, len], _ =>
    simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of' hb.2.1
    have hd := agree_of' hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPost pb) _ m m₂ r
    dsimp only [Curry.apply, ctrFinalPost, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hc]
    exact h

/-- `ctrFinalPost` reads the memory on entry only within the buffers. -/
theorem ctrFinalPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrFinalSig.words pb) (ctrFinalPost pb) vs m₁ m' r →
      Curry.apply (ctrFinalSig.words pb) (ctrFinalPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [k, ctr, data, len], _ =>
    simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of' hb.1
    have hc := agree_of' hb.2.1
    have hd := agree_of' hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrFinalPost pb) _ m₂ m' r
    dsimp only [Curry.apply, ctrFinalPost, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [scheduleAt_congr hk, bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega),
      bytesAt_congr' hc]
    exact h

end VG.Proof.Sm4
