module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
public import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Invoke the existing native RSA array operations inside the exact FFDH
scratch subview, then restore the caller's original memory permissions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem viewLarge {s : State} {base : BitVec 32} {capacity w : Nat}
    (h : KeyReady base capacity w s) : 96 < 8 * capacity := by
  have fit := h.arrayFit (j := 0) (by decide)
  simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
  omega

theorem keyClrTop_ok {s : State} {base : BitVec 32} {capacity w j : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bound : j < 30) :
    WP isa (.block (VG.Impl.Rsa.Arm.Recover.clrTop j)) s fun t =>
      KeyReady base capacity w t ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [j] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) j =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w j ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := by
  have fits : base.toNat + 96 < 2 ^ 32 := by
    have := workspace.nowrap
    have := viewLarge ready
    omega
  have proof := VG.Proof.Rsa.Arm.Recover.clrTop_ok ready bound (by decide) (by omega)
    (rest := []) (Q := fun t => VG.Proof.Rsa.Arm.Keys.Ws t (base + 96#32) (8 * capacity - 96)
      (2 * w + 2) 30 ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [j] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) j =
        Proof.Rsa.Mont.numAt s.mem (State.addr base) w j ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs (s.withRegions s.rd [keyViewRegion base capacity]) t)
    (fun t ht keep value rest => WP.block_nil ⟨ht, keep, by
      rw [show 2 * w + 2 - 2 = 2 * w by omega] at value
      exact value.trans (keyView_low s.mem base w j fits), rest⟩)
  simp only [List.append_nil] at proof
  refine keyView_inline workspace (viewLarge ready) proof rfl ?_
  rintro t rd wr frame ⟨ht, keep, value, rest⟩
  exact ⟨by simpa only [KeyReady, rd] using ht, keep, value, rest_of_keyView rest rd wr⟩

theorem keyClrLow_ok {s : State} {base : BitVec 32} {capacity w j : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bound : j < 30) :
    WP isa (.block (VG.Impl.Rsa.Arm.Keys.clrLow j)) s fun t =>
      KeyReady base capacity w t ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [j] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) j =
        2 * (VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) j / 2) ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := by
  have proof := VG.Proof.Rsa.Arm.Keys.clrLow_ok ready bound (by decide)
    (rest := []) (Q := fun t => VG.Proof.Rsa.Arm.Keys.Ws t (base + 96#32) (8 * capacity - 96)
      (2 * w + 2) 30 ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [j] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) j =
        2 * (VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) j / 2) ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs (s.withRegions s.rd [keyViewRegion base capacity]) t)
    (fun t ht keep value rest _ => WP.block_nil ⟨ht, keep, value, rest⟩)
  simp only [List.append_nil] at proof
  refine keyView_inline workspace (viewLarge ready) proof rfl ?_
  rintro t rd wr frame ⟨ht, keep, value, rest⟩
  exact ⟨by simpa only [KeyReady, rd] using ht, keep, value, rest_of_keyView rest rd wr⟩

theorem keyCopy_ok {s : State} {base : BitVec 32} {capacity w o a : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (outBound : o < 30) (inBound : a < 30) (different : o ≠ a) :
    WP isa (VG.Impl.Rsa.Arm.Keys.copy o a) s fun t =>
      KeyReady base capacity w t ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [o] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) o =
        VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) a ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := by
  refine keyView_inline workspace (viewLarge ready)
    (VG.Proof.Rsa.Arm.Keys.copy_ok ready outBound inBound (by decide) different) (by rfl) ?_
  rintro t rd wr frame ⟨ht, keep, value, rest, _⟩
  exact ⟨by simpa only [KeyReady, rd] using ht, keep, value, rest_of_keyView rest rd wr⟩

theorem keySub3_ok {s : State} {base : BitVec 32} {capacity w o a b : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (outBound : o < 30) (aBound : a < 30) (bBound : b < 30) (oa : o ≠ a) (ob : o ≠ b) :
    WP isa (VG.Impl.Rsa.Arm.Keys.sub3 o a b) s fun t =>
      KeyReady base capacity w t ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [o] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) o +
        VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) b =
        VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) a +
          Nat.pow 2 (32 * (2 * w + 2)) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := by
  refine keyView_inline workspace (viewLarge ready)
    (VG.Proof.Rsa.Arm.Keys.sub3_ok ready outBound aBound bBound (by decide) oa ob) (by rfl) ?_
  rintro t rd wr frame ⟨ht, keep, value, borrow, rest⟩
  exact ⟨by simpa only [KeyReady, rd] using ht, keep, value, borrow, rest_of_keyView rest rd wr⟩

theorem keyHalf_ok {s : State} {base : BitVec 32} {capacity w j : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bound : j < 30) (carry : (s.gpr .r11).toNat ≤ 1) :
    WP isa (VG.Impl.Rsa.Arm.Keys.half j) s fun t =>
      KeyReady base capacity w t ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [j] [] s.mem t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * w + 2) j =
        (VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) j +
          Nat.pow 2 (32 * (2 * w + 2)) * (s.gpr .r11).toNat) / 2 ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := by
  refine keyView_inline workspace (viewLarge ready)
    (VG.Proof.Rsa.Arm.Keys.half_ok ready bound (by decide) carry) (by rfl) ?_
  rintro t rd wr frame ⟨ht, keep, value, rest⟩
  exact ⟨by simpa only [KeyReady, rd] using ht, keep, value, rest_of_keyView rest rd wr⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
