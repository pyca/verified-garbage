module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# What RSA's postconditions read of the memory on return (x86, 32-bit)

The lemmas from which RSA's functions on x86 prove that their
postconditions read the memory on return only within their buffers
(`X86.Scrub.PostOut`, with `X86.Scrub.postOut_of_local_pre`): the octets and
words at an address read only the bytes there (`bytesAt_of`, `wordsAt_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Reading memory only within the buffers -/

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N * 1⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N * 1⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ N) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hn]))).symm

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

/-- An argument word, as the function reads it (its low 32 bits), is at most
the word. -/
theorem toNat_sw_le (A : Abi isa) (hA : ScrubAbi A) (x : BitVec 64) : (x.setWidth A.ptrBits).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth, hA.ptrBits]
  exact Nat.mod_le _ _

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

end VG.Proof.Rsa.X86.Scrub
