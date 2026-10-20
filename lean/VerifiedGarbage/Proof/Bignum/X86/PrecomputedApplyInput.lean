module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInput
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApply
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExportSafe
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PublicExport
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Import, apply, and export the representative using the stored public key -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedApplyInput_ok {s : State} {base : Addr} {bytes len m r e : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (N : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) = m)
    (R : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) = r)
    (E : val32 s.mem base 128 2 = e) (gt : 1 < m) (odd : m % 2 = 1) (rb : r < m) :
    WP isa (VG.Impl.Bignum.X86.PrecomputedFn.applyInput (Spec.Rsa.modulusWords len)) s fun t =>
      let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len)
      t.gpr .eax = BitVec.ofNat 32 (decide (x < m)).toNat ∧
      (r = 2 ^ (128 * Spec.Rsa.modulusWords len) % m → m < 2 ^ (8 * len) →
        Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < m then x ^ e % m else 0) len) ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have space := h.space
  have nw := h.scratch.nowrap
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have b6 := slot_bound (n := (Spec.Rsa.modulusWords len)) (i := 6) (by decide)
  have d6 := slot_header (Spec.Rsa.modulusWords len) 6
  have s06 := slot_le (n := (Spec.Rsa.modulusWords len)) (i := 0) (j := 6) (by decide)
  have s56 := slot_le (n := (Spec.Rsa.modulusWords len)) (i := 5) (j := 6) (by decide)
  simp only [stride] at b6 s06 s56
  unfold VG.Impl.Bignum.X86.PrecomputedFn.applyInput
  refine WP.seq (WP.mono (precomputedInput_ok h.scratch dims.1 h.space (by have := h.lower; omega)
    dims.2.2 (h.stack 6 (by decide)) (by rw [← h.inLen]; exact h.stack 7 (by decide))
    h.inFit h.inRead h.inApart) fun u ⟨X, O, K⟩ => ?_)
  have hu := h.keep K (by decide) (by decide) (O.mono (by omega) (by omega))
  have Nu : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) = m := by
    rw [wordsVal_eq_val32, O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]; exact N
  have Ru : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) = r := by
    rw [wordsVal_eq_val32, O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]; exact R
  have Eu : val32 u.mem base 128 2 = e := by
    rw [O.val32 (.inl (by omega)) (by decide), E]
  refine WP.seq (WP.mono (precomputedAcceptAndPower_ok hu.scratch dims.1 h.space Nu X Eu gt odd Ru rb)
    fun v ⟨_, _, V, Mask, Ov, Kv⟩ => ?_)
  have Os : Outside base 16 (bytes - 16) s.mem v.mem :=
    (O.mono (by omega) (by omega)).trans Ov
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (Os.mono (by omega) (by omega))
  let accept := decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) < m)
  have AM : v.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0 := by
    simpa only [accept, decide_eq_true_eq] using Mask
  have DP := hv.stack 0 (by decide)
  have DL : CallArgument v base bytes 1 (BitVec.ofNat 32 len) := by rw [← h.outLen]; exact hv.stack 1 (by decide)
  obtain ⟨trace, t, Exec, Return, Frame, Keep⟩ := precomputedExport_safe hv.scratch dims.1 h.space
    (by have := h.lower; omega) dims.2.2 accept AM DP DL h.outFit hv.outWrite h.outApart
  refine ⟨trace, t, Exec, Return, ?_, ?_, Ks.trans Keep⟩
  · intro good fit
    have Y := V good
    have Fit : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) ^ e % m < 2 ^ (8 * len) :=
      Nat.lt_trans (Nat.mod_lt _ (by omega)) fit
    have Result := VG.Proof.Dsa.X86.wp_result (exportResult_ok hv.scratch dims.1 h.space
      (by have := h.lower; omega) dims.2.2 Y Fit accept AM DP DL h.outFit hv.outWrite h.outApart) Exec
    simpa only [accept, decide_eq_true_eq] using Result.1
  · exact ((outside_frame Os (by omega)).mono (by simp)).trans Frame

end VG.Proof.Bignum.X86.PublicContext
