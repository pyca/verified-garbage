module

public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ChaCha20: the locality lemma of its residue proofs

On every target: a streaming state whose first 136 bytes are unchanged
represents the same key and keystream (`Proof/ChaCha20/X86_64/Scrub.lean`,
`Proof/ChaCha20/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.ScrubLocal

open VG.Spec.ChaCha20

/-- A state whose first 136 bytes are unchanged represents the same key and
keystream. -/
theorem stream_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 136, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    keyAt m' p = keyAt m p ∧ restAt m' p = restAt m p ∧ leftAt m' p = leftAt m p := by
  have hb : ∀ a n, a + n ≤ 136 → bytesAt m' (p + BitVec.ofNat 64 a) n = bytesAt m (p + BitVec.ofNat 64 a) n :=
    fun a n hn => List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      simpa only [VG.Offset.add_add] using h (a + i) (by omega_using [hn, this])
  have hw : ∀ a w, a + w / 8 ≤ 136 → m'.readW (p + BitVec.ofNat 64 a) w = m.readW (p + BitVec.ofNat 64 a) w :=
    fun a w hn => Mem.readW_congr fun i hi => by
      simpa only [VG.Offset.add_add] using h (a + i) (by omega_using [hn, hi])
  have hl : leftAt m' p = leftAt m p := by
    simp only [leftAt]; rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, hw _ _ (by decide)]
  have hs : stateAt m' p = stateAt m p := by
    apply Vector.ext; intro i hi
    simp only [stateAt, Vector.getElem_ofFn]
    exact hw _ _ (by omega_using [hi])
  refine ⟨by simp only [keyAt]; exact hb 16 32 (by decide), ?_, hl⟩
  simp only [restAt, hl, hs]
  rw [hb _ _ (by omega_using [])]

end VG.Proof.ChaCha20.ScrubLocal
