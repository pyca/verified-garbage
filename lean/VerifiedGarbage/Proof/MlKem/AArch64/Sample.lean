module

public import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
meta import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall

/-!
# ML-KEM on AArch64: the memory of `SampleNTT`'s loop

A polynomial of zeros is zero byte by byte (`byte_zero`), and a byte of a
region is at an offset below its length (`at_off`), for the constant-time
proofs of the samplers: two runs that agree on the SHAKE128 output and
start from zeros in `a` agree on all the memory the loop touches.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Constant time -/

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyRegion p).Contains y 1) : m y = 0 := by
  simp only [Region.Contains] at hy
  have e : y = coeffAddr p ((y - p).toNat / 4) + BitVec.ofNat 64 ((y - p).toNat % 4) := by
    rw [coeffAddr, ptr_add, show 4 * ((y - p).toNat / 4) + (y - p).toNat % 4 = (y - p).toNat by omega_using []]
    bv_omega
  rw [e, Mem.readW_byte m _ (by omega_using []), ← coeffAt_eq, h _ (by omega_using [hy])]
  ext i hi
  simp

/-- A byte of a region, at its offset. -/
theorem at_off {b y : Addr} {len : Nat} (hy : (⟨b, len⟩ : Region).Contains y 1) :
    ∃ p < len, y = b + BitVec.ofNat 64 p := by
  simp only [Region.Contains] at hy
  exact ⟨(y - b).toNat, by omega_using [hy], by bv_omega⟩

end VG.Proof.MlKem.AArch64.Sample
