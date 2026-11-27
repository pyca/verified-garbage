module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesCbc.Wipe
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES: the locality lemmas of its residue proofs

On every target: the bytes and blocks a postcondition reads agree between
two memories that agree on the buffer they lie in
(`Proof/Aes/X86_64/ModesScrub.lean`, `Proof/Aes/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.ScrubLocal

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this])

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega_using [hn])
  simpa using this

theorem blocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 16 ≤ L) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n :=
  Proof.AesCbc.Wipe.blocksAt_congr fun i hi => agree_le h hn i (by omega_using [hi])

end

end VG.Proof.Aes.ScrubLocal
