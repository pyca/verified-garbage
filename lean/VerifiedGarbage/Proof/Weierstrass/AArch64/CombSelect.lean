module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.CombDigit
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# The comb on AArch64: the constant-time selection

The masks of the magnitude `a` (`MasksOf`): `maskReg m` all ones exactly for
`m = a` (`a ≤ 8`), which code that writes only `x2`, `x4` and `x9` keeps
(`MasksOf.keep`), and a word ANDed with a mask (`bmask_and`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open CombCfg

/-- The masks of the magnitude `a`. -/
def MasksOf (s : State) (a : Nat) : Prop := ∀ m ≤ 8, s.gpr (maskReg m) = bmask (decide (a = m))

theorem maskRegs_not : ∀ m ≤ 8, maskReg m ≠ .x2 ∧ maskReg m ≠ .x4 ∧ maskReg m ≠ .x9 ∧
    maskReg m ≠ .x0 ∧ maskReg m ≠ .x19 := by decide

theorem MasksOf.keep {s s' : State} {a : Nat} (h : MasksOf s a) (hk : Keeps [.x2, .x4, .x9] s s') :
    MasksOf s' a := fun m hm => by
  have := maskRegs_not m hm
  rw [hk.gpr _ (by simp [this.1, this.2.1, this.2.2.1])]
  exact h m hm

theorem bmask_and (v : BitVec 64) (b : Bool) : v &&& bmask b = if b then v else 0 := by
  cases b
  · simp [bmask]
  · exact BitVec.and_allOnes

theorem MasksOf.keepRegs {s s' : State} {a : Nat} (h : MasksOf s a)
    (hk : KeepRegs [.x2, .x4, .x9] s s') : MasksOf s' a := fun m hm => by
  have := maskRegs_not m hm
  rw [hk.gpr _ (by simp [this.1, this.2.1, this.2.2.1])]
  exact h m hm

theorem rotateRight_zero' (x : BitVec 64) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

end VG.Proof.Weierstrass.AArch64
