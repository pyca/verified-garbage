module

public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.AArch64.DiagonalChainMath`, which this module and modules that import it used -/

section

/-! Carry conservation for a doubled word stream and a two-word addend. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

abbrev shifted (a p : BitVec 64) : BitVec 64 := (a ++ p).extractLsb' 63 64

theorem shifted_nat (a p : BitVec 64) :
    (shifted a p).toNat = (2*a.toNat + p.toNat / 2^63) % 2^64 := by
  simp only [shifted, BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_eq_div_pow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt p.isLt, Nat.shiftLeft_eq]
  congr 1
  omega_arith

theorem shifted_pair (x y p : BitVec 64) :
    (shifted x p).toNat + 2^64*(shifted y x).toNat + 2^128*(y.toNat/2^63) =
      2*(x.toNat+2^64*y.toNat) + p.toNat/2^63 := by
  rw [shifted_nat, shifted_nat]
  have hx := x.isLt; have hy := y.isLt; have hp := p.isLt
  omega_arith

abbrev carry (s : State) : Nat := (s.gpr .x5).toNat / 2^63 + s.c.toNat

theorem pair_val (al ah x y p : BitVec 64) (c : Bool) :
    let lo := shifted x p + al + BitVec.ofNat 64 c.toNat
    let c₁ := decide (2^64 ≤ (shifted x p).toNat + al.toNat + c.toNat)
    let hi := shifted y x + ah + BitVec.ofNat 64 c₁.toNat
    let c₂ := decide (2^64 ≤ (shifted y x).toNat + ah.toNat + c₁.toNat)
    lo.toNat + 2^64*hi.toNat + 2^128*(y.toNat/2^63+c₂.toNat) =
      2*(x.toNat+2^64*y.toNat) + al.toNat + 2^64*ah.toNat + p.toNat/2^63+c.toNat := by
  dsimp only
  have hl := adc_toNat (shifted x p) al c
  have hh := adc_toNat (shifted y x) ah
    (decide (2^64 ≤ (shifted x p).toNat + al.toNat + c.toNat))
  rw [Square.boolWord] at hl hh
  have hd := shifted_pair x y p
  omega_arith

end VG.Proof.Bignum.AArch64.DiagonalChain

end

end

/-! Execute the single addition carry chain without dropping the shift bit. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem carry_bound (s : State) : carry s ≤ 2 := by
  have h := (s.gpr .x5).isLt
  have hc := Bool.toNat_le s.c
  unfold carry
  omega_arith

theorem exec_extr63 {s : State} {d n m : Reg} :
    exec (.extr .x d n m 63) s =
      some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' 63 64)) := rfl

theorem core_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.DiagonalChain.core) s fun t =>
      ((t.gpr .x3).toNat + 2^64*(t.gpr .x6).toNat + 2^128*carry t =
        2*((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat) +
          (s.gpr .x2).toNat+2^64*(s.gpr .x1).toNat+carry s ∧
        t.mem = s.mem) ∧ Keep [.x3,.x5,.x6] s t := by
  refine WP.keep [.x3,.x5,.x6] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.DiagonalChain.core
  brun [exec_extr63, carry]
  simpa only [carry, shifted, off, BitVec.ofNat_add, BitVec.add_assoc, Nat.add_assoc] using
    pair_val (s.gpr .x2) (s.gpr .x1) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) s.c

end VG.Proof.Bignum.AArch64.DiagonalChain
