module

public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Data.Int.Basic
/-! # Execute the three-product inverse lift without memory accesses -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/InverseLift.lean`, which only this module imported.
section

/-! # A one-step negative-inverse lift expressed in native-word parts -/

section
namespace VG.Proof.RsaKeyGen

theorem inverse_lift_identity {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    c * (x + b * y) + 1 = b * b * (k * k - c * q) := by
  grind

theorem inverse_lift_dvd {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    b * b ∣ c * (x + b * y) + 1 :=
  ⟨k * k - c * q, inverse_lift_identity inverse split⟩

theorem inverse_lift_nat {b c x : Nat} (inverse : (c * x + 1) % b = 0) :
    (c * (x + b * (x * ((c * x + 1) / b) % b)) + 1) % (b * b) = 0 := by
  let k := (c * x + 1) / b
  have eq₁ : c * x + 1 = b * k := by
    have := Nat.div_add_mod (c * x + 1) b
    rw [inverse, Nat.add_zero] at this
    exact this.symm
  have eq₂ : x * k = b * (x * k / b) + x * k % b := (Nat.div_add_mod (x * k) b).symm
  have I : (c : Int) * x + 1 = (b : Int) * k := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using congrArg (fun n : Nat => (n : Int)) eq₁
  have S : (x : Int) * k = (b : Int) * (x * k / b : Nat) + (x * k % b : Nat) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) eq₂
  have D : ((b * b : Nat) : Int) ∣ ((c * (x + b * (x * k % b)) + 1 : Nat) : Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using inverse_lift_dvd I S
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp D)

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

def highCarry (a x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (a.toNat * x.toNat / 2 ^ 32) +
    Trial.carryWord (Trial.carry (BitVec.ofNat 32 (a.toNat * x.toNat)) 1)

def upper (a b x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (x.toNat *
    (BitVec.ofNat 32 (b.toNat * x.toNat) + highCarry a x).toNat)

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .eax = upper (s.gpr .ebx) (s.gpr .esi) (s.gpr .ecx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_mul fun b B => wp_addS rfl fun c C cfC =>
    wp_adcS rfl cfC fun d D _ => ?_
  have Kd : Keeps [.eax, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have high : d.gpr .edx = highCarry (s.gpr .ebx) (s.gpr .ecx) := by
    rw [D.gpr, C.other .edx (by decide), B.edx, A.gpr, A.other .ecx (by decide)]
    change _ + 0#32 + _ = _
    rw [BitVec.add_zero, B.eax, A.gpr, A.other .ecx (by decide)]
    rfl
  refine wp_movS rfl fun e E _ => wp_movS rfl fun f F _ => wp_mul fun h H =>
    wp_addS rfl fun i I _ => wp_movS rfl fun j J _ => wp_movS rfl fun k K _ =>
    wp_mul fun t T => WP.block_nil ?_
  have keep : Keeps [.eax, .edx, .ebp] s t :=
    (((((((Kd.mono (by decide)).widen E.keeps).widen F.keeps).widen H.keeps).widen I.keeps).widen
      J.keeps).widen K.keeps).widen T.keeps
  refine ⟨?_, ?_, keep⟩
  · rw [T.eax, K.gpr, J.other .ecx (by decide), I.other .ecx (by decide),
      H.other .ecx (by decide) (by decide), F.other .ecx (by decide), E.other .ecx (by decide),
      Kd.1 .ecx (by decide), K.other .ebp (by decide), J.gpr, I.gpr, H.eax, F.gpr,
      E.other .esi (by decide), Kd.1 .esi (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), Kd.1 .ecx (by decide), H.other .ebp (by decide) (by decide),
      F.other .ebp (by decide), E.gpr, high]
    rfl
  · rw [T.mem, K.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

theorem highCarry_toNat (a x : BitVec 32) :
    (highCarry a x).toNat = (a.toNat * x.toNat + 1) / 2 ^ 32 := by
  have product := Nat.mul_le_mul (show a.toNat ≤ 2 ^ 32 - 1 by have := a.isLt; omega)
    (show x.toNat ≤ 2 ^ 32 - 1 by have := x.isLt; omega)
  have split := Nat.div_add_mod (a.toNat * x.toNat) (2 ^ 32)
  have remainder := Nat.mod_lt (a.toNat * x.toNat) (by decide : 0 < 2 ^ 32)
  unfold highCarry
  rw [BitVec.toNat_add, Trial.carryWord_toNat, Trial.carry_toNat]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

theorem upper_toNat (a b x : BitVec 32) :
    (upper a b x).toNat =
      x.toNat * ((a.toNat * x.toNat + 1) / 2 ^ 32 + b.toNat * x.toNat) % 2 ^ 32 := by
  unfold upper
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, highCarry_toNat]
  rw [Nat.mod_add_mod, Nat.mul_mod_mod]
  congr 2
  omega

theorem upper_inverse (a b x : BitVec 32)
    (inverse : (a.toNat * x.toNat + 1) % 2 ^ 32 = 0) :
    ((a.toNat + 2 ^ 32 * b.toNat) * (x.toNat + 2 ^ 32 * (upper a b x).toNat) + 1) % 2 ^ 64 = 0 := by
  have rearrange : (a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1 =
      a.toNat * x.toNat + 1 + 2 ^ 32 * (b.toNat * x.toNat) := by grind
  have full : ((a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1) % 2 ^ 32 = 0 := by
    rw [rearrange, Nat.add_mul_mod_self_left]
    exact inverse
  have result := VG.Proof.RsaKeyGen.inverse_lift_nat full
  rw [rearrange, Nat.add_mul_div_left _ _ (by decide)] at result
  rw [upper_toNat]
  exact result

theorem inverse_ok (s : State)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .ecx).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block code) s fun t =>
      (((s.gpr .ebx).toNat + 2 ^ 32 * (s.gpr .esi).toNat) *
        ((t.gpr .ecx).toNat + 2 ^ 32 * (t.gpr .eax).toNat) + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t :=
  WP.mono (code_ok s) fun t ⟨value, mem, keep⟩ =>
    ⟨by rw [value, keep.1 .ecx (by decide)]; exact upper_inverse _ _ _ inverse, mem, keep⟩

end VG.Proof.RsaKeyGen.X86.InverseLift
