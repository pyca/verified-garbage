module

public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Blowfish: the locality lemmas of its residue proofs

On every target: the memory a postcondition reads agrees between two
memories that agree on the buffers it reads (`Proof/Blowfish/X86_64/Scrub.lean`,
`Proof/Blowfish/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.ScrubLocal

open VG.Spec.Blowfish

section

variable {m₁ m₂ : Mem}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem blocksAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n * 8 ≤ L) : blocksAt m₂ p n = blocksAt m₁ p n := by
  have h := agree_of h hn
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 8 * i + j.val < n * 8 := by have := j.isLt; omega_arith
  rw [VG.Offset.add_add]
  exact h _ this

theorem cbcBlocksAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n * 8 ≤ L) : cbcBlocksAt m₂ p n = cbcBlocksAt m₁ p n := by
  simp only [cbcBlocksAt, blocksAt_of h hn]

theorem bytesAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have h := agree_of h hn
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem scheduleAt_of {p : Addr} (h : ∀ a, Region.Contains ⟨p, 4168 * Elem.u8.size⟩ a 1 → m₁ a = m₂ a) :
    scheduleAt m₂ p = scheduleAt m₁ p :=
  scheduleAt_congr (agree_of h (Nat.le_refl _))





end

end VG.Proof.Blowfish.ScrubLocal
