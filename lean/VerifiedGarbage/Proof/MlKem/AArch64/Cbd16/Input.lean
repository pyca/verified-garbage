module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Byte
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Input bytes and the CBD2 specification -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem G_nibble (s : State) {i : Nat} (hi : i < 256) :
    (Cbd2.G s i).toNat =
      ((nibble (BitVec.ofNat 8 (Cbd2.byte s (i/2))) (i%2 != 0)).toNat + 3327)%3329 := by
  have hv := (Cbd2.B s).getD (i/2) 0 |>.isLt
  have hn := (nibble_values (Cbd2.byte s (i/2)) hv (i%2 != 0)).2
  rw [hn, Cbd2.G, samplePolyCBD2_val _ (show i < n from hi)]
  have hmod : (cbdX (VG.Proof.MlKem.nibble (Cbd2.B s) i) + q -
    cbdY (VG.Proof.MlKem.nibble (Cbd2.B s) i))%q < 2^32 := by
    have := Nat.mod_lt (cbdX (VG.Proof.MlKem.nibble (Cbd2.B s) i) + q -
      cbdY (VG.Proof.MlKem.nibble (Cbd2.B s) i)) (show 0<q by decide)
    exact Nat.lt_trans this (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmod]
  unfold VG.Proof.MlKem.nibble
  rcases (by omega : i%2 = 0 ∨ i%2 = 1) with h | h <;> simp [h,q,Cbd2.byte]

end VG.Proof.MlKem.AArch64.Cbd16
