module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # The inverse and persistent banks reuse the runtime RSA clear proof -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.Rsa.X86.Keys (hdr)

theorem clear_ok {s : State} {B : Addr} {Z n N k : Nat} (h : Ws s B Z n N)
    (w : Width) (hw : w ≠ .correction) (positive : 0 < k) (bound : k ≤ N) :
    WP isa (clear w k) s fun t => Ws t B Z n N ∧
      Outside B hdr (4 * (k * (w.words n + 2))) s.mem t.mem ∧
      (∀ j < k, val32 t.mem B (Loc.offset n (.array w j)) (w.words n + 2) = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have H := h.runtime hw
  have code : clear w k = VG.Impl.Rsa.X86.KeyRt.zeroArrays w.lay k := by
    cases w <;> simp_all [clear]
  rw [code]
  have core := VG.Proof.Rsa.X86.KeyRt.zeroArrays_ok H positive bound
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, O, V, K⟩ => ?_
  have fit := H.ws.fits
  rw [kw_words h.width] at fit
  have bound' : hdr + 4 * (k * (w.words n + 2)) ≤ Z := by
    have le := Nat.mul_le_mul_right (w.words n + 2) bound
    simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S] at fit
    rw [Nat.mul_left_comm] at fit
    omega
  simp only [VG.Proof.Rsa.X86.Keys.arr, Nat.zero_mul, Nat.add_zero] at O
  refine ⟨h.keep K (O.mono (Nat.zero_le _) (by omega)), O, ?_, K⟩
  simpa only [Loc.offset, VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
    VG.Impl.Rsa.X86.Keys.slot, VG.Impl.Rsa.X86.Keys.stride] using V

end VG.Proof.RsaKeyGen.X86.KeyRuntime
