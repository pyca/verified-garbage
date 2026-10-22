module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Framework.Contract

/-! # A prepared candidate-three workspace shared by valid-input examples -/

@[expose] public section
namespace VG.Proof.MillerRabin.Example
open VG
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

/-- A four-limb prepared working space for the candidate 3. -/
def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

theorem sat_layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact satMem 0x1000 256 := by
  simp only [Spec.MillerRabin.Layout, Spec.MillerRabin.compact, Spec.Rsa.Mont.Layout,
    Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
  decide +kernel

theorem sat_prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact satMem 0x1000 := by
  have hw : wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : numAt satMem 0x1000 4 0 = 3 := by decide +kernel
  have h5 : numAt satMem 0x1000 4 5 = 2 := by decide +kernel
  have h9 : numAt satMem 0x1000 4 9 = 1 := by decide +kernel
  have h10 : numAt satMem 0x1000 4 10 = 2 := by decide +kernel
  have h27 : numAt satMem 0x1000 4 27 = 1 := by decide +kernel
  simp only [Spec.MillerRabin.Prepared, Spec.MillerRabin.compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

end VG.Proof.MillerRabin.Example
