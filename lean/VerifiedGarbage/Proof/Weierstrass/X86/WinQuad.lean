module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Weierstrass.X86.TComb

/-!
# The x86 window loop's frame and Jacobian doublings

The table survives each iteration's writes. The accumulator is converted
from homogeneous to Jacobian coordinates for four doublings, then converted
back. `WinFlags` and `WinFinish` handle the point at infinity.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

open Spec.Weierstrass

variable {F : Impl.Weierstrass.Mont.Modulus}

/-! ## The loop -/

/-! ## Four doublings in Jacobian coordinates -/

/-- What a program reads is in `V`. -/
local macro "rcb_sub" : tactic => `(tactic| plain_simp_names (
                   intro x hx
                   simp only [rcbR, WinCfg.zeroPt, List.cons_append, List.nil_append, List.mem_cons,
                     List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))

end VG.Proof.Weierstrass.X86
