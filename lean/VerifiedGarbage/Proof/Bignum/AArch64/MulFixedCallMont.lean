module

public import VerifiedGarbage.Impl.Bignum.AArch64.MulFixedCall
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall

/-! # The eight-limb Montgomery products, the repeated ones by calls

`Mont.productEight`, but the products of `MulFixedCall.shared` call their
fixed-index helper (`vg_rsa_mul_{o}_{a}_{b}`), which runs the same code, as
`Mont.calledSquareEight` calls the squares' (`SquareCall.call_ok`). -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.MulFixedCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem shared_keepsLink : MulFixedCall.shared.all (fun t =>
    (ProductDispatch.mm t.1 t.2.1 t.2.2).allInstrs (fun i => vdstOf i != some .v31)) = true := by
  decide +kernel

theorem no_v31 {o a b : Nat} (h : (o, a, b) ∈ MulFixedCall.shared) :
    ∀ i ∈ instrs (ProductDispatch.mm o a b), vdstOf i ≠ some .v31 := by
  have hk := List.all_eq_true.mp shared_keepsLink _ h
  rw [Code.allInstrs_eq, List.all_eq_true] at hk
  intro i hi he
  have hn := hk i hi
  rw [he] at hn
  contradiction

end VG.Proof.Bignum.AArch64.MulFixedCall

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def Mont.calledProductEight : Mont where
  mm := VG.Impl.Bignum.AArch64.MulFixedCall.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    unfold VG.Impl.Bignum.AArch64.MulFixedCall.mm
    by_cases h : (o, a, b) ∈ VG.Impl.Bignum.AArch64.MulFixedCall.shared
    · rw [ite_eq_left h]
      exact SquareCall.call_ok Mont.productEight (MulFixedCall.no_v31 h)
        hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    · rw [ite_eq_right h]
      exact Mont.productEight.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
  ct := by
    intro o a b huse
    unfold VG.Impl.Bignum.AArch64.MulFixedCall.mm
    by_cases h : (o, a, b) ∈ VG.Impl.Bignum.AArch64.MulFixedCall.shared
    · rw [ite_eq_left h]
      exact SquareCall.wrapper_ct (Mont.productEight.ct huse)
    · rw [ite_eq_right h]
      exact Mont.productEight.ct huse

end VG.Proof.Bignum.AArch64
