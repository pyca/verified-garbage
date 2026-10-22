module

public import VerifiedGarbage.Proof.MillerRabin.X86.ABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! Construct the unchanged shared cdecl contract from its resource view. -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem round_pre_of {s : State} (A : RoundABI s) :
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pre s := by
  rcases A with ⟨low, bound, rd, wr, args, ret, below, fit, layout, prepared⟩
  have address : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4#64 := by
    change VG.Proof.Bignum.X86.byteAddr (s.gpr .esp + 4#32) = _
    exact VG.Proof.Bignum.X86.byteAddr_add (k := 4) (by omega)
  have retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩ := by
    rw [address]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have belowArgs : (⟨(s.gpr .esp).setWidth 64 - 1172#64, 1172⟩ : Region).Disjoint
      ⟨argAddr s 0, 8⟩ := by
    rw [address]
    exact (Offset.disjoint_below _ (by decide)).symm
  sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal,
    argBytes, stackBelow]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | exact args.symm
    | exact below

end VG.Proof.MillerRabin.X86
