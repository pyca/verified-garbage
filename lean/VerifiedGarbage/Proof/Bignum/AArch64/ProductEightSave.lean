module

import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Bignum.AArch64.Run

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev savedLanes : List (Reg × VReg × Nat) :=
  (VG.Impl.Bignum.AArch64.ProductEight.regs.zip VG.Impl.Bignum.AArch64.ProductEight.vecs).map
    fun (r, v) => (r, v, 0)

theorem saves_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.ProductEight.saves) s fun t =>
      (t.mem = s.mem ∧ ∀ k ∈ savedLanes, laneOf t k.2.1 k.2.2 = s.gpr k.1) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl (by decide +kernel)
  change WP isa (.block (insOf savedLanes)) s _
  exact WP.mono (insOf_ok savedLanes s (by decide) (by decide))
    fun _ ⟨_, hm, _, _, _, hl, _⟩ => ⟨hm, hl⟩

theorem restores_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.ProductEight.restores) s fun t =>
      (t.mem = s.mem ∧ ∀ k ∈ savedLanes, t.gpr k.1 = laneOf s k.2.1 k.2.2) ∧
        Keep VG.Impl.Bignum.AArch64.ProductEight.regs s t := by
  refine WP.keep VG.Impl.Bignum.AArch64.ProductEight.regs ?_ rfl rfl (by decide +kernel)
  change WP isa (.block (umovOf savedLanes)) s _
  exact WP.mono (umovOf_ok savedLanes s (by decide) (by decide))
    fun _ ⟨hm, _, _, _, hl, _⟩ => ⟨hm, hl⟩

/-- The column loop cannot overwrite any saved scalar register's vector lane. -/
theorem columns_noVec :
    (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock).allInstrs
      (fun i => (vdstOf i).isNone) = true := by
  decide +kernel

end VG.Proof.Bignum.AArch64.ProductEight
