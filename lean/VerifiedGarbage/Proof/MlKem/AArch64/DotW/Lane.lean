module
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64: lanes

The halfwords of a vector of 16-bit coefficients (`hlanes_coeffs`), the even
and odd coefficients of eight pairs (UZP1, UZP2: `gatherW_lanes`), and the
products of halfwords accumulated in words (UMLAL, UMLAL2: `umlal_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The halfwords of `x` are `f`. -/
def HLanes (x : BitVec 128) (f : Nat → Nat) : Prop := ∀ e < 8, (vhalf x e).toNat = f e

theorem lanes_ofVWords {g : Nat → BitVec 32} {F : Nat → Nat} (h : ∀ e < 4, (g e).toNat = F e) :
    Lanes (ofVWords (g 0) (g 1) (g 2) (g 3)) F := fun e he => by
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> exact h _ (by decide)

/-- Eight 16-bit coefficients from `j` in a vector. -/
theorem hlanes_coeffs (m : Mem) (p : Addr) (j : Nat) {F : Nat → Nat}
    (h : ∀ e < 8, (coeffAtW 16 m p (j + e)).toNat = F e) :
    HLanes (m.read (p + BitVec.ofNat 64 (2 * j)) 16) F := fun e he => by
  rw [vhalf_read_coeff m p j he]; exact h e he

/-- The even and odd coefficients of eight pairs, from two vectors of sixteen. -/
theorem gatherW_lanes {x y : BitVec 128} {A : Nat → Nat}
    (hx : HLanes x A) (hy : HLanes y (fun e => A (8 + e))) :
    HLanes (VPermOp.eval .uzp1 .h8 x y) (fun e => A (2 * e)) ∧
    HLanes (VPermOp.eval .uzp2 .h8 x y) (fun e => A (2 * e + 1)) := by
  constructor
  · intro e he
    rw [Ntt16.vhalf_perm_h8 _ _ _ he]
    dsimp only
    split
    · exact hx _ (by omega)
    · rw [hy _ (by omega)]; dsimp only; congr 1; omega
  · intro e he
    rw [Ntt16.vhalf_perm_h8 _ _ _ he]
    dsimp only
    split
    · exact hx _ (by omega)
    · rw [hy _ (by omega)]; dsimp only; congr 1; omega

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `umlal d, n, m` (or `umlal2`): lanes `p + e` of the halfwords' products added to the words
of `d`, `p = 4` for `umlal2`. -/
theorem umlal_ok {hi : Bool} {d n m : VReg} {A X Y : Nat → Nat}
    (ha : Lanes (s.v d) A) (hx : HLanes (s.v n) X) (hy : HLanes (s.v m) Y)
    (hlt : ∀ e < 4, A e + X ((if hi then 4 else 0) + e) * Y ((if hi then 4 else 0) + e) < 2 ^ 32)
    (k : ∀ s', VChg [d] s s' →
      Lanes (s'.v d) (fun e => A e + X ((if hi then 4 else 0) + e) * Y ((if hi then 4 else 0) + e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.vop (.umlalH hi d n m) :: rest)) s Q := by
  refine wp_vop rfl fun s' h => k s' h.chg ?_
  rw [h.v]
  refine lanes_ofVWords (g := fun e => vword (s.v d) e +
    (vhalf (s.v n) ((if hi then 4 else 0) + e)).setWidth 32 *
      (vhalf (s.v m) ((if hi then 4 else 0) + e)).setWidth 32) fun e he => ?_
  have hp : (if hi then 4 else 0) + e < 8 := by split <;> omega
  have hl := hlt e he
  have hX := hx _ hp
  have hY := hy _ hp
  have hx16 := (vhalf (s.v n) ((if hi then 4 else 0) + e)).isLt
  have hy16 := (vhalf (s.v m) ((if hi then 4 else 0) + e)).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, ha e he]
  rw [Nat.mod_eq_of_lt (a := (vhalf (s.v n) _).toNat) (by omega),
    Nat.mod_eq_of_lt (a := (vhalf (s.v m) _).toNat) (by omega), hX, hY,
    Nat.mod_eq_of_lt (show X _ * Y _ < 2 ^ 32 by omega), Nat.mod_eq_of_lt hl]

end

end VG.Proof.MlKem.AArch64.DotW
