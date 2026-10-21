module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Form the inverse-modulus validity bit through a public runtime pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem oddFlag_ok {s : State} {B : Addr} {Z n N input : Nat}
    (h : Ws s B Z n N) (hi : input < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block (oddFlag input)) s fun t => Ws t B Z n N ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if (s.gpr .ebx).toNat = 0 then num s.mem B n input % 2 else 0) ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have fit := h.arr_fit hi
  have nowrap := h.old.workspace.nowrap
  unfold oddFlag
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun u U _ => wp_subS rfl fun v V _ => ?_
  have Kv : Keeps [.eax] s v := U.keeps.trans V.keeps
  have mv : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.ptr_ok (arr input) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fit; omega)
    fun w Kw mw P => ?_
  have hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine wp_logicS (.inl rfl) (VG.Proof.Mont.X86.Rt.readSrc_ptr hw.full.rt P
    (d := 0) (by simp only [arr, offset_array, Width.words]
                 unfold VG.Proof.Rsa.X86.Keys.S at fit; omega)) fun x X => ?_
  refine wp_logicS (.inl rfl) rfl fun y Y => ?_
  have K : Keeps [.eax, .edx, .ebp] s y :=
    ((Kv.mono (by decide)).trans (Kw.mono (by decide))).trans
      ((X.keeps.mono (by decide)).trans (Y.keeps.mono (by decide)))
  have memory : y.mem = s.mem := Y.mem.trans (X.mem.trans (mw.trans mv))
  have hy := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have value : y.gpr .eax = ((1 : BitVec 32) - s.gpr .ebx) &&&
      s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n input)) 32 &&& (1 : BitVec 32) := by
    rw [Y.gpr, X.gpr, Kw.1 _ (by decide), V.gpr, U.gpr, U.other _ (by decide),
      mw, V.mem, U.mem, Nat.add_zero, arr, offset_array, Width.words]
    rfl
  refine WP.mono (store_slot hy (d := kFlag) (by decide) .eax) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, value, VG.Proof.RsaKeyGen.X86.Key.odd_mask _ _ bit,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity s.mem B h.wpos input]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
