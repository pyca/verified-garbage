module
import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine

import VerifiedGarbage.Proof.Dsa.X86.DigestClamp
import VerifiedGarbage.Proof.Dsa.X86.DigestWidth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! # The DSA digest-prefix length from validated subgroup masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem digestPrefix_raw {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 8256 ≤ size) :
    WP isa Shape.digestPrefix s fun t =>
      (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat
          ((shapeWord s base 48 &&& 28) ||| (shapeWord s base 44 &&& 20) ||| (shapeWord s base 52 &&& 32)).toNat ∧
      Keeps [.eax, .ebx, .edx] s t ∧ Outside base (Layout.field .digestPrefixLen) 4 s.mem t.mem := by
  unfold Shape.digestPrefix
  refine WP.block_append (WP.mono (digestWidth_ok hs (by omega)) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  refine WP.mono (digestClamp_ok (hs.of_keeps Ku (by decide)) hz) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).trans Kt, Mu ▸ Ot⟩
  rw [Vt, Vu]
  simp only [shapeWord, Mu]

end VG.Proof.Dsa.X86
