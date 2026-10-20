module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightAccumulate
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight

def finishColumn (k : Nat) : List Instr :=
  [st .x19 .x16 (8*k), mov .x19 .x20, mov .x20 .x21, movi .x21 0]

theorem finishColumn_ok {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (he : e + 8 * k + 8 ≤ Z) (hk : k < 15) :
    WP isa (.block (finishColumn k)) s fun t =>
      (t.mem = s.mem.writeW (off B (e + 8*k)) (s.gpr .x19) ∧
        (s.gpr .x19).toNat + 2 ^ 64 * accValue t = accValue s ∧
        accValue t < 2 ^ 128) ∧ Keep [.x19, .x20, .x21] s t := by
  refine WP.keep [.x19, .x20, .x21] ?_ rfl rfl rfl
  have enc : 8*k % 8 = 0 ∧ 8*k < 32768 := ⟨by omega, by omega⟩
  unfold finishColumn accValue
  brun [h16, enc, hs.st he]
  simp only [show (BitVec.setWidth 64 (0#16)).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  constructor
  · omega
  · have h20 := (s.gpr .x20).isLt
    have h21 := (s.gpr .x21).isLt
    omega

/-- One emitted triangular column, with the exact stored word and remaining
carry. The frame is just its single output word. -/
theorem column_ok {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (he : e + 8 * k + 8 ≤ Z) (hk : k < 15)
    (h7 : s.gpr .x7 = 0) (hb : accValue s < 2 ^ 128) :
    WP isa (.block (column k)) s fun t =>
      (word t.mem B (e + 8*k)).toNat + 2 ^ 64 * accValue t =
        accValue s + pairSum s (pairs k) (pairs k).length ∧
      accValue t < 2 ^ 128 ∧ Outside B (e + 8*k) 8 s.mem t.mem ∧ Keep workRegs s t := by
  change WP isa (.block ((product (pairs k) 0 ++ product (pairs k) 1 ++
    steps (pairs k) (pairs k).length) ++ finishColumn k)) s _
  apply WP.block_append
  refine WP.mono (column_accumulate_ok hk h7 hb) fun u ⟨hu, hum, ku⟩ => ?_
  refine WP.mono (finishColumn_ok (hs.congr ku.wr)
    ((ku.gpr _ (by decide)).trans h16) he hk) fun t ⟨⟨htm, htv, htb⟩, kt⟩ => ?_
  have hn := hs.nowrap
  refine ⟨?_, htb, ?_, (ku.trans kt).mono (by simp [workRegs])⟩
  · rw [htm, word_writeW_self]
    exact htv.trans hu
  · have ho := writeW_outside u.mem B (u.gpr .x19) (d := e + 8*k) (by omega)
    intro x hx
    exact ((congrArg (fun m : Mem => m x) htm).trans (ho x hx)).trans
      (congrArg (fun m : Mem => m x) hum)

end VG.Proof.Bignum.AArch64.SquareEight
