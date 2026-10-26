module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.RsaKeyGen.TopWord32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Read the high modulus word through its public runtime address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.RsaKeyGen.X86.Key (aN kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem topBit_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block topBit) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if 2 ^ (32 * n - 1) ≤ num s.mem B n aN then 1 else 0) ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have fits := h.arr_fit (j := aN) (by decide)
  have positive := h.wpos
  have nowrap := h.old.workspace.nowrap
  unfold topBit
  refine h.ptr_ok (arr aN) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fits; omega)
    fun u Ku mu Pu => ?_
  have hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok .modulus .edx fun v Kv mv count => ?_
  change (v.gpr .edx).toNat = 4 * n at count
  refine wp_addS rfl fun w W _ => wp_subS rfl fun x X _ => ?_
  have Kx : Keeps [.ebp, .edx] s x := (Ku.trans (Kv.mono (by decide))).trans
    ((W.keeps.mono (by decide)).trans (X.keeps.mono (by decide)))
  have mx : x.mem = s.mem := X.mem.trans (W.mem.trans (mv.trans mu))
  have hx := h.keep Kx (by rw [mx]; exact Outside.refl _ _ _ _)
  have Px : PtrAt x B .ebp (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) := by
    rw [PtrAt, X.gpr, W.gpr, BitVec.toNat_sub, BitVec.toNat_add,
      Kv.1 _ (by decide), Pu, count]
    simp only [arr, offset_array, Width.words] at *
    simp only [show (4 : BitVec 32).toNat = 4 by rfl]
    unfold VG.Proof.Rsa.X86.Keys.S at fits
    omega
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hx.full.rt Px (d := 0)
    (by unfold VG.Proof.Rsa.X86.Keys.S at fits; omega)) fun y Y _ => ?_
  refine wp_shr (by decide) fun z Zf _ => ?_
  have K : Keeps [.eax, .edx, .ebp] s z := (Kx.mono (by decide)).trans
    ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide)))
  have memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans mx)
  have hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .eax) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, Zf.gpr, Y.gpr, mx, Nat.add_zero,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change w32 s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN + 4 * (n - 1)) / 2 ^ 31 = _
  rw [← VG.Proof.RsaKeyGen.WordBounds32.top_div positive]
  change num s.mem B n aN / 2 ^ (32 * n - 1) = _
  have bound := val32_lt s.mem B (VG.Proof.Rsa.X86.Keys.arr n aN) n
  change num s.mem B n aN < 2 ^ (32 * n) at bound
  have factor : 2 ^ (32 * n) = 2 ^ (32 * n - 1) * 2 := by
    calc
      2 ^ (32 * n) = 2 ^ ((32 * n - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = _ := Nat.pow_succ ..
  rw [factor] at bound
  split
  · next H => exact Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul] using H) (by omega)
  · next H => exact Nat.div_eq_of_lt (by omega)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
