module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Ed25519.Word64
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEightRaw
open VG.Proof.MlKem.AArch64 (Keep)

theorem firstCarry_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (he : e + 72 ≤ Z) :
    WP isa (.block (carryWord 0)) s fun t =>
      (∃ v : Word, t.mem = s.mem.writeW (off B (e+64)) v ∧
        v.toNat + 2 ^ 64 * t.c.toNat = (word s.mem B (e+64)).toNat + (s.gpr .x10).toNat) ∧
          Keep [.x13] s t := by
  refine WP.keep [.x13] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.SquareEightRaw.carryWord
  brun [h16, hs.ld he, hs.st he]
  refine ⟨_, rfl, ?_⟩
  simpa only [addCarry, VG.Proof.Ed25519.Word64.carryOut, Bool.toNat_false, Nat.add_zero] using
    addCarry_value (word s.mem B (e+64)) (s.gpr .x10) false

theorem nextCarry_ok {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e + 8*(k+8) + 8 ≤ Z) (hk : 0 < k) (hk' : k < 7) :
    WP isa (.block (carryWord k)) s fun t =>
      (∃ v : Word, t.mem = s.mem.writeW (off B (e+8*(k+8))) v ∧
        v.toNat + 2 ^ 64 * t.c.toNat = (word s.mem B (e+8*(k+8))).toNat + s.c.toNat) ∧
          Keep [.x13] s t := by
  have enc : (8*(k+8)) % 8 = 0 ∧ 8*(k+8) < 32768 := by omega
  unfold VG.Impl.Bignum.AArch64.SquareEightRaw.carryWord
  rw [show (k == 0) = false by simp [Nat.ne_of_gt hk]]
  simp only [Bool.false_eq_true, ite_false]
  refine WP.keep [.x13] ?_ rfl rfl rfl
  brun [h16, h7, enc, hs.ld he, hs.st he]
  refine ⟨_, rfl, ?_⟩
  simpa only [addCarry, VG.Proof.Ed25519.Word64.carryOut, show (0 : Word).toNat = 0 from rfl, Nat.add_zero] using
    addCarry_value (word s.mem B (e+8*(k+8))) 0 s.c

end VG.Proof.Bignum.AArch64.SquareEight
