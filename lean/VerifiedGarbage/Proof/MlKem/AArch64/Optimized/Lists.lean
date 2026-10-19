module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Symbol preservation through lists of sequential operations -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.WPs
open VG VG.AArch64

theorem mono_syms : ∀{cs : List (Prog isa)} {s : State} {Q R : State → Prop},
    WPs cs s Q → (∀t, Q t → t.syms=s.syms → R t) → WPs cs s R
  | [],s,_,_,h,k => k s h rfl
  | _::_,_,_,_,h,k => WP.mono_syms h fun _ ht hs =>
      mono_syms ht (fun u hu hu' => k u hu (hu'.trans hs))

end VG.Proof.MlKem.AArch64.WPs
