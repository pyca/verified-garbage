module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcMath
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! AArch64 Montgomery cancellation setup and pending-carry tail. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem redcHead_ok {s : State} {B : Addr} {Z e eN : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (h10 : s.gpr .x10 = off B eN)
    (h15 : s.gpr .x15 = minv) (h7 : s.gpr .x7 = 0) (hZ : e+8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.redcHead) s fun t =>
      (t.gpr .x1 = redcU (word s.mem B e) minv ∧
        t.gpr .x16 = off B e ∧ t.gpr .x17 = off B eN ∧
        t.gpr .x2 = 0 ∧ t.c = false ∧ t.mem = s.mem) ∧ Keep [.x1, .x2, .x3, .x16, .x17] s t := by
  refine WP.keep [.x1, .x2, .x3, .x16, .x17] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.redcHead
  brun [h8, h10, h15, h7, hs.ld hZ]
  rfl

theorem redcTail_ok {s : State} {B : Addr} {Z e w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e)
    (h16 : s.gpr .x16 = off B (e+8*w)) (h7 : s.gpr .x7 = 0)
    (hZ : e+8*w+8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.redcTail) s fun t =>
      (∃ lo : BitVec 64, t.mem = s.mem.writeW (off B (e+8*w)) lo ∧
        lo.toNat + 2 ^ 64*(t.gpr .x5).toNat =
          (word s.mem B (e+8*w)).toNat + (s.gpr .x2).toNat + (s.gpr .x5).toNat ∧
        ((s.gpr .x5).toNat ≤ 1 → (t.gpr .x5).toNat ≤ 1) ∧
        t.gpr .x8 = off B (e+8) ∧ t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1) ∧
      Keep [.x3, .x5, .x6, .x8, .x13] s t := by
  refine WP.keep [.x3, .x5, .x6, .x8, .x13] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.redcTail
  brun [h8, h16, h7, hs.ld hZ, hs.st hZ]
  simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64, zero_add64]
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [carry2_nat]
    exact add3_val (word s.mem B (e+8*w)) (s.gpr .x2) (s.gpr .x5)
  · rw [carry2_nat]
    intro hp
    have hv := add3_val (word s.mem B (e+8*w)) (s.gpr .x2) (s.gpr .x5)
    dsimp only at hv
    have hx := (word s.mem B (e+8*w)).isLt
    have hc := (s.gpr .x2).isLt
    dsimp only [word] at hv hx ⊢
    omega_arith

end VG.Proof.Bignum.AArch64.Square
