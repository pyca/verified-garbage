module

import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
public import VerifiedGarbage.Proof.Curve448.AArch64.Swap
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Ed448 verification on AArch64: the words of a table entry

Untrusted: everything here is checked by Lean. Word `w` of entry `e` of the
table at `TAB` (`tw`), and where word `w` of the selected entry goes, in
slots 6–8 (`dst`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside store_ok)
open VG.Proof.Curve448.AArch64 (mask)

/-! ## A word of the entry -/

/-- Word `w` of entry `m` of the table. -/
def tw (m : Mem) (base : Addr) (e w : Nat) : BitVec 64 := word m base (TAB + 192 * e + 8 * w)

/-- Where word `w` of the selected entry goes: slots 6–8, eight words each. -/
def dst (w : Nat) : Nat := slot (6 + w / 8) + 8 * (w % 8)

theorem dst_bounds {w : Nat} (hw : w < 24) : 832 ≤ dst w ∧ dst w + 8 ≤ 1216 ∧ dst w % 8 = 0 := by
  simp only [dst, slot]; omega_arith

end VG.Proof.Ed448.AArch64.Window
