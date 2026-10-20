module
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def store : List Instr :=
  [.vop (.perm .zip1 .s4 .v0 .v21 .v23), .vop (.perm .zip2 .s4 .v1 .v21 .v23),
   .strq .v0 .x0 0, .strq .v1 .x0 16]

def interleave (A B : Nat → Nat) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (if i % 2 = 0 then A (i/2) else B (i/2))

theorem zip1_values {x y : BitVec 128} {A B : Nat → Nat}
    (hx : Lanes x A) (hy : Lanes y B) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x y) e = interleave A B e := by
  rw [vword_zip1_s4' _ _ he]
  unfold interleave
  split <;> rename_i h
  · exact BitVec.eq_of_toNat_eq (by rw [hx _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt (by omega))])
  · exact BitVec.eq_of_toNat_eq (by rw [hy _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hy.lt (by omega))])

theorem zip2_values {x y : BitVec 128} {A B : Nat → Nat}
    (hx : Lanes x A) (hy : Lanes y B) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip2 .s4 x y) e = interleave A B (4+e) := by
  rw [vword_zip2_s4 _ _ he]
  unfold interleave
  have hm : (4+e)%2 = e%2 := by omega
  have hd : (4+e)/2 = 2+e/2 := by omega
  rw [hm,hd]
  split <;> rename_i h
  · exact BitVec.eq_of_toNat_eq (by rw [hx _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt (by omega))])
  · exact BitVec.eq_of_toNat_eq (by rw [hy _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hy.lt (by omega))])

theorem store_ok {s : State} {p : Addr} {j : Nat} {A B : Nat → Nat}
    (hx0 : s.gpr .x0 = coeffAddr p j) (hj : j+8 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (coeffAddr p (j+4*i)) 16)
    (hc : VConsts s) (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v23) B)
    {O D : Nat → BitVec 32} (ho : CoeffsUpTo s.mem p j O D)
    (hv : ∀ e < 8, O (j+e) = interleave A B e) :
    WP isa (.block store) s fun s' => Keep [] s s' ∧ VConsts s' ∧
      Frame [polyRegion p] s.mem s'.mem ∧ CoeffsUpTo s'.mem p (j+8) O D := by
  simp only [store]
  refine wp_vop (d := .v0) rfl fun s₁ h₁ => wp_vop (d := .v1) rfl fun s₂ h₂ => ?_
  refine wp_strq (a := coeffAddr p j) (by decide)
    (by rw [h₂.gpr,h₁.gpr,hx0,ptr_zero])
    (by rw [h₂.wr,h₁.wr]; simpa only [Nat.mul_zero,Nat.add_zero] using hw 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_strq (a := coeffAddr p (j+4)) (by decide)
    (by rw [h₃.gpr,h₂.gpr,h₁.gpr,hx0,coeffAddr_step])
    (by rw [h₃.wr,h₂.wr,h₁.wr]; exact hw 1 (by decide)) fun s₄ h₄ => wp_nil ?_
  have hm : s₄.mem = (s.mem.write (coeffAddr p j) 16
      (VPermOp.eval .zip1 .s4 (s.v .v21) (s.v .v23))).write (coeffAddr p (j+4)) 16
      (VPermOp.eval .zip2 .s4 (s.v .v21) (s.v .v23)) := by
    rw [h₄.mem,h₃.mem,h₂.mem,h₁.mem,h₃.v,h₂.v,h₁.get .v21,h₁.get .v23,h₂.get .v0,h₁.v]
  refine ⟨(((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono,
    ⟨?_,?_⟩, ?_, ?_⟩
  · rw [h₄.v,h₃.v,h₂.get .v16,h₁.get .v16]; exact hc.q
  · rw [h₄.v,h₃.v,h₂.get .v17,h₁.get .v17]; exact hc.m
  · rw [hm]; exact frame16 (frame16 (Frame.refl _ _) (by omega) _) (by omega) _
  · rw [hm,show j+8 = j+4+4 by omega]
    refine CoeffsUpTo.write16 (CoeffsUpTo.write16 ho (by omega) (fun e he => ?_)) (by omega) (fun e he => ?_)
    · rw [hv e (by omega)]; exact zip1_values ha hb he
    · rw [show j+4+e = j+(4+e) by omega,hv (4+e) (by omega)]; exact zip2_values ha hb he

end VG.Proof.MlKem.AArch64.Dot
