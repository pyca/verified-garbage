module

import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightWord
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Bignum.AArch64.Square

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight
open VG.Proof.MlKem.AArch64 (Keep)

def loadInputs : List Instr := inputs.zipIdx.map fun (r,i) => ld r .x8 (8*i)

theorem loadInputs_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block loadInputs) s fun t =>
      ((∀ i < 8, t.gpr inputs[i]! = word s.mem B (e + 8*i)) ∧
        t.mem = s.mem) ∧ Keep inputs s t := by
  have hl : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (e + 8*i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep inputs ?_ (by decide) (by decide) (by decide)
  have hc : loadInputs =
    [ld .x2 .x8 0, ld .x3 .x8 8, ld .x4 .x8 16, ld .x5 .x8 24,
      ld .x6 .x8 32, ld .x9 .x8 40, ld .x11 .x8 48, ld .x27 .x8 56] := rfl
  brun [hc, h8, hs.ld (show e + 8 ≤ Z by omega), hl 0 (by decide), hl 1 (by decide),
    hl 2 (by decide), hl 3 (by decide), hl 4 (by decide), hl 5 (by decide),
    hl 6 (by decide), hl 7 (by decide)]
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem inputs_value {s : State} {m : Mem} {B : Addr} {e n : Nat}
    (hi : ∀ i < n, s.gpr inputs[i]! = word m B (e + 8*i)) :
    Square.value (2 ^ 64) (fun i => (s.gpr inputs[i]!).toNat) n = wv m B e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.value, wv, ih (fun i h => hi i (by omega)), hi n (by omega),
      ← Nat.pow_mul, Nat.mul_comm (word m B (e + 8*n)).toNat]

theorem inputs_cross {s : State} {m : Mem} {B : Addr} {e n : Nat}
    (hi : ∀ i < n, s.gpr inputs[i]! = word m B (e + 8*i)) :
    Square.cross (2 ^ 64) (fun i => (s.gpr inputs[i]!).toNat) n = Square.crossValue m B e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.cross, Square.crossValue_succ, ih (fun i h => hi i (by omega)),
      inputs_value (fun i h => hi i (by omega)), hi n (by omega), ← Nat.pow_mul]

def clearAcc : List Instr := [movi .x19 0, movi .x20 0, movi .x21 0]

theorem clearAcc_ok (s : State) :
    WP isa (.block clearAcc) s fun t =>
      (accValue t = 0 ∧ t.mem = s.mem) ∧ Keep [.x19, .x20, .x21] s t := by
  refine WP.keep [.x19, .x20, .x21] ?_ rfl rfl rfl
  unfold clearAcc accValue
  brun []

end VG.Proof.Bignum.AArch64.SquareEight
