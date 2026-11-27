module

public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia: the locality lemmas of its residue proofs

On every target: the memory a postcondition reads agrees between two
memories that agree on the buffers it reads (`Proof/Camellia/X86_64/Scrub.lean`,
`Proof/Camellia/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.ScrubLocal

open VG.Spec.Camellia

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) :=
  fun i hi => Proof.Camellia.agree_of h i (by omega_using [hn, hi])

theorem aesBytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => agree_le h hn i (List.mem_range.mp hi)

theorem cbcBlocksAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 16 ≤ L) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_arith)

theorem blocksAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 16 ≤ L) :
    blocksAt m₂ p n = blocksAt m₁ p n :=
  Proof.Camellia.blocksAt_congr fun i hi => agree_le h hn i (by omega_using [hi])

end

end VG.Proof.Camellia.ScrubLocal
