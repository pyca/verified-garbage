module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.Mont.WriteWord32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

/-! # Construct the private-exponent retry bound at the runtime width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.Rsa.X86.Keys (aT1)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem smallConstant_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa smallConstant s fun t => Ws t B Z n 32 ∧ Keep B n [aT1] [] s.mem t.mem ∧
      num t.mem B n aT1 = 2 ^ (16 * n) + 1 ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit (j := aT1) (by decide)
  have nowrap := h.old.workspace.nowrap
  have positive := h.wpos
  have width := h.width
  have half : 32 * (n / 2) = 16 * n := by omega_arith
  unfold smallConstant
  refine WP.seq (WP.mono (constant_ok h (by decide) (1 : BitVec 32)) fun u ⟨hu, Ou, one, Ku⟩ => ?_)
  change num u.mem B n aT1 = 1 at one
  refine hu.ptr_ok (arr aT1) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold S at fit; omega_arith)
    fun v Kv mv Pv => ?_
  have hv := hu.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.bytes_ok .prime .edx fun w Kw mw count => ?_
  change (w.gpr .edx).toNat = 4 * (n / 2) at count
  refine wp_addS rfl fun x X _ => wp_movS rfl fun y Y _ => ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] u y := (Kv.mono (by decide)).trans
    ((Kw.mono (by decide)).trans ((X.keeps.mono (by decide)).trans (Y.keeps.mono (by decide))))
  have memory : y.mem = u.mem := Y.mem.trans (X.mem.trans (mw.trans mv))
  have hy := hu.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have Py : PtrAt y B .ebp (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2)) := by
    rw [PtrAt, Y.other _ (by decide), X.gpr, VG.Proof.Mont.X86.Rt.ptr_add]
    · rw [count]
    · rw [PtrAt, Kw.1 _ (by decide)]; exact Pv
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hy.full.rt Py (d := 0)
    (by unfold S at fit; omega_arith)) (VG.Proof.Mont.X86.Rt.ws_write hy.full.rt
      (by unfold S at fit; omega_arith)) fun t T => WP.block_nil ?_
  have mem : t.mem = u.mem.writeW
      (off B (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2))) (1 : BitVec 32) := by
    rw [T.mem, memory, Y.gpr, Nat.add_zero]
  have Ot : Outside B (VG.Proof.Rsa.X86.Keys.arr n aT1 + 4 * (n / 2)) 4 u.mem t.mem := by
    rw [mem]; exact writeW32_outside _ _ _ (by unfold S at fit; omega_arith)
  have frame := Ou.trans (VG.Proof.Rsa.X86.Keys.Keep.of_arr Ot
    (by unfold S; omega_arith) (by simp))
  have value : num t.mem B n aT1 = 2 ^ (16 * n) + 1 := by
    rw [num, mem, VG.Proof.Mont.val32_write_word _ _ _ (by omega_arith : n / 2 < n)
      (by unfold S at fit; omega_arith)]
    · change num u.mem B n aT1 + 2 ^ (32 * (n / 2)) * 1 = _
      rw [one, half, Nat.mul_one, Nat.add_comm]
    · change num u.mem B n aT1 < _
      rw [one]
      have bound := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega_arith : 1 ≤ 32 * (n / 2))
      omega_arith
  have Kt := Ku.trans (K.trans (T.keeps _))
  exact ⟨h.afterKeep Kt frame (by decide) (by simp), frame, value, Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
