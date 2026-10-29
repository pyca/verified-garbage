module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Small
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Recognize a unit gcd in any of the shared inverse banks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S)
open VG.Impl.Rsa.X86.Keys (aT1 aT2 sT)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem gcdIsOne_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    (h : Ws s B Z n N) (space : 15 ≤ N) (hw : w ≠ .correction) :
    WP isa (gcdIsOne w) s fun t => Ws t B Z n N ∧
      Keep B (w.words n) [aT2, aT1] [sT, kFlag] s.mem t.mem ∧
      VG.Proof.Rsa.X86.Keys.slot t.mem B kFlag = (if num s.mem B (w.words n) 1 = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have H := h.runtime hw
  have fit := H.ws.arr_fit (j := aT2) (by unfold aT2; omega)
  have f1 := H.ws.fit64 (j := 1) (by omega)
  have positive := H.ws.wpos
  rw [kw_words h.width] at fit f1 positive
  unfold gcdIsOne
  refine WP.seq (WP.mono (small_ok h w 1 (by rw [offset_array]; exact fit))
    fun u ⟨hu, Ou, V, Ku⟩ => ?_)
  rw [offset_array] at Ou V
  change val32 u.mem B (VG.Proof.Rsa.X86.Keys.arr (w.words n) aT2) (w.words n + 2) = 1 at V
  have ou : Keep B (w.words n) [aT2] [] s.mem u.mem :=
    VG.Proof.Rsa.X86.Keys.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou)
      (by simp only [S]; omega) (by simp)
  have constant : num u.mem B (w.words n) aT2 = 1 := by
    have bound : 1 < 2 ^ (32 * w.words n) := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ 32 * w.words n)
      omega
    exact (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : w.words n ≤ w.words n + 2)
      (by rw [V]; exact bound)).trans V
  have core := VG.Proof.Rsa.X86.KeyRt.eqS_ok (d := kFlag) (a := 1) (b := aT2) (t := aT1) (hu.runtime hw)
    (by unfold aT1; omega) (by omega) (by unfold aT2; omega)
    (by decide) (by decide) (by decide)
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, Ot, result, Kt⟩ => ?_
  have original : num u.mem B (w.words n) 1 = num s.mem B (w.words n) 1 :=
    ou.num (by decide) (by simp) f1
  rw [original, constant] at result
  refine ⟨hu.afterBank hw Kt Ot (by intro j hj; have hsmall :=
      (by decide : ∀ j ∈ ([aT1] : List Nat), j < 15) j hj; omega) (by decide),
    ou.join Ot (js := [aT2, aT1]) (ds := [sT, kFlag]), result, (Ku.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
