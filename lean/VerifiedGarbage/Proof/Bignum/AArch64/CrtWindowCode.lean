module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatch
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block

/-!
# RSA with the CRT on AArch64: correctness

`code`, from a state its contract allows, writes `privateCrt` of its inputs
(`crtCode_correct`), against `crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA)

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`. -/
theorem crtCode_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : crtA.pre s) :
    ∃ t s', Exec isa (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtA.post s s' := by
  have c := crtCtx_of h
  clear h
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) s fun s' => abiPreserved s s' ∧ crtA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold VG.Impl.Rsa.AArch64.WindowFive.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (h₁.keep.gpr .x2 (by decide))
    (by rw [h₁.keep.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
    (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (s.gpr .x3).toNat) (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false := by simpa using hb
    exact WP.mono (crtFail_ok hpre)
      fun t hp => crtCode_fin h₁ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true := by simpa using hb
    exact WP.mono (dispatch_ok W M S hpre hv) fun t ⟨Mk, hp, hiff⟩ => crtCode_fin h₁ k₂ hp
      (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.AArch64.WindowFive
