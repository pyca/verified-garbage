module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Pure
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! # Byte-lane identities for Camellia's register substitution -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial

theorem vbyte_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (x y : BitVec 128) (e : Nat) (he : e < 16) :
    vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) :=
by
  unfold VArr.map2
  exact vbyte_ofVBytes (fun i => f 8 (vbyte x i) (vbyte y i)) he

theorem vbyte_and (x y : BitVec 128) (e : Nat) :
    vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [vbyte, hi]

theorem dup_byte (x : BitVec 64) (e : Nat) (he : e < 16) :
    vbyte (ofVDwords x x) e = byte x (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, ofVDwords, byte, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8*e+i < 64 by omega, ite_true, Nat.mod_eq_of_lt h]
  · simp only [show ¬8*e+i < 64 by omega, ite_false]
    congr 1
    omega

/-- SHL followed by SRI implements a byte rotation, including the inserted bit. -/
theorem shift_insert_rotate : ∀ sh ∈ [1,7], ∀ x : Byte,
    ((x <<< sh) &&& ~~~(BitVec.allOnes 8 >>> (8-sh))) ||| (x >>> (8-sh)) =
      x.rotateLeft sh := by
  decide +kernel

theorem byte_select_zero (x y : Byte) : x ^^^ ((x ^^^ y) &&& 0) = x := by simp

theorem byte_select_all (x y : Byte) : x ^^^ ((x ^^^ y) &&& 255) = y := by
  change x ^^^ ((x ^^^ y) &&& BitVec.allOnes 8) = y
  rw [BitVec.and_allOnes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

/-- Rotate selected byte lanes while preserving all scalar state and the table. -/
theorem rotateSelected_run (s : State) (mask : VReg) (sh : Nat)
    (hm1 : mask ≠ .v1) (hsh : sh ∈ [1,7]) :
    ∃ t, runBlock isa (rotateSelected mask sh) s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e =
        vbyte (s.v .v0) e ^^^
          ((vbyte (s.v .v0) e ^^^ (vbyte (s.v .v0) e).rotateLeft sh) &&&
            vbyte (s.v mask) e)) ∧
      VOnly [.v0,.v1] s t := by
  let a := s.setV .v1 (VArr.b16.map2
    (fun w x y => VShiftOp.shl.eval sh w x y) (s.v .v1) (s.v .v0))
  let b := a.setV .v1 (VArr.b16.map2
    (fun w x y => VShiftOp.sri.eval (8-sh) w x y) (a.v .v1) (a.v .v0))
  let c := b.setV .v0 (VSelOp.bit.eval (b.v .v0) (b.v .v1) (b.v mask))
  have hs : VShiftOp.shl.ok 8 sh = true := by
    rcases (show sh = 1 ∨ sh = 7 by simpa using hsh) with rfl | rfl <;> rfl
  have ht : VShiftOp.sri.ok 8 (8-sh) = true := by
    rcases (show sh = 1 ∨ sh = 7 by simpa using hsh) with rfl | rfl <;> rfl
  refine ⟨c,?_,?_,?_⟩
  · simp only [rotateSelected,runBlock_cons]
    rw [show exec (.vop (.shift .shl .b16 .v1 .v0 sh)) s = some a by
      simp [exec_vop',VOp.eval,VArr.esize,hs,a]]
    simp only [runStep_some,runBlock_cons]
    rw [show exec (.vop (.shift .sri .b16 .v1 .v0 (8-sh))) a = some b by
      simp [exec_vop',VOp.eval,VArr.esize,ht,b]]
    simp only [runStep_some,runBlock_cons]
    rfl
  · intro e he
    simp only [c,b,a,State.setV,ite_true,show (.v0 : VReg) ≠ .v1 by decide,
      hm1,ite_false,VSelOp.eval,
      vbyte_xor,vbyte_and,vbyte_map2 _ _ _ e he,VShiftOp.eval]
    rw [shift_insert_rotate sh hsh]
  · exact ((VOnly.setV s (by simp) _).trans
      (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)

theorem low64_eq_packed (v : BitVec 128) (t : Nat → Byte)
    (h : ∀ j < 8, vbyte v j = t j) : v.extractLsb' 0 64 = packed t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h₁ := congrArg (fun b : Byte => b.getLsbD (i%8)) (h (i/8) (by omega))
  have h₂ := congrArg (fun b : Byte => b.getLsbD (i%8))
    (byte_packed t (i/8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i%8 < 8 by omega,
    decide_true, Bool.true_and, show 8*(i/8)+i%8=i by omega] at h₁
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    show i%8 < 8 by omega, decide_true, Bool.true_and,
    show 8*(i/8)+i%8=i by omega] at h₂
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,Nat.zero_add]
  exact h₁.trans h₂.symm

end VG.Proof.Camellia.AArch64.Serial
