module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (256 * t), L s₀ - 256 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 256 * t ≤ L s₀) :
    Region.Sub (tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 256 * t) (ht : 256 * t ≤ L s₀) :
    ¬ (tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

end VG.Proof.ChaCha20.AArch64.Neon4
