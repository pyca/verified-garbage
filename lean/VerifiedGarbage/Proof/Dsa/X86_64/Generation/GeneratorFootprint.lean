module
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.X86_64.Call

import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Global memory footprint of the reused generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Impl.Bignum.X86_64

theorem generator_power_frame {B : Addr} {len : Nat} {m m' : Mem}
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hf : CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len m m') :
    Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] m m' := by
  have hsize : pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have sub : Region.Sub ⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ ⟨B, activeBytes⟩ :=
    Offset.sub_base B (by omega)
  intro a ha
  have hn := ha ⟨B, activeBytes⟩ (by simp)
  have hn' : ¬ (⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ : Region).Contains a 1 :=
    fun hc => hn (sub a hc)
  apply hf a
  · right
    change ¬ ofs B a < activeBytes at hn
    unfold activeBytes at hn
    omega
  · intro r hr
    right
    have hb := (workRanges_ok (len / 8) r hr).2
    change ¬ ofs (off B pWorkspace) a < slot (len / 8) 8 + tabBytes (len / 8) at hn'
    omega
  · intro i hi he
    apply ha ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by rcases hl with hh | hh | hh <;> omega)

end VG.Proof.Dsa.X86_64.Generation
