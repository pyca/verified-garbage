module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedChecks
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckExponent
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApplyPost
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPostFrame
import VerifiedGarbage.Proof.Bignum.PackedFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Validate packed arithmetic inputs and choose a safe public-operation path -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedChecked_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (N : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) =
      wv s.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len))
    (R : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) =
      wv s.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len))
    (E : val32 s.mem base 128 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true) :
    WP isa (.seq (precomputedChecks (Spec.Rsa.modulusWords len))
      (.ite .e VG.Impl.Bignum.X86.PublicFn.failure (VG.Impl.Bignum.X86.PrecomputedFn.applyInput (Spec.Rsa.modulusWords len)))) s
      fun t => PrecomputedPost base bytes len args s.mem t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := h.scratch.nowrap
  have sz := h.space
  have size := size_eq (Spec.Rsa.modulusWords len)
  have dims := h.dimensions
  refine WP.seq (WP.mono (precomputedChecks_ok h.scratch dims.1 h.space) fun u ⟨_, Z, O, K⟩ => ?_)
  have Os := precomputedCheck_saved O h.space
  have Os' : Outside base 0 bytes s.mem u.mem := Os.mono (by omega) (by omega)
  have hu := h.keep K (by decide) (by decide) Os'
  have M := scratch_wv Os' (by omega) (by omega) (n := Spec.Rsa.modulusWords len)
    (d := 0) (by omega) (by omega) h.preApart
  have P := scratch_wv Os' (by omega) (by omega) (n := Spec.Rsa.modulusWords len)
    (d := 8 * Spec.Rsa.modulusWords len) (by omega) (by omega) h.preApart
  have EB := scratch_bytes Os' (by have := h.eBound; have := h.upper; omega) h.eApart
  have Nu : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) =
      wv u.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len) := by
    rw [precomputedCheck_value O (by decide : 0 < 8) (by decide) (by decide) (by omega), N, M]
  have Ru : wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) =
      wv u.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len) := by
    rw [precomputedCheck_value O (by decide : 5 < 8) (by decide) (by decide) (by omega), R, P]
  rw [N, R, ← M, ← P] at Z
  refine WP.ite (!precomputedAccepted (wv u.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len))
    (wv u.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len))) Z ?_ ?_
  · intro rejected
    have failed : ∀ nB : List Byte, nB.length = len →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt u.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
        Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt u.mem (byteAddr (args 4)) (args 5).toNat)
          (Spec.Rsa.bytesAt u.mem (byteAddr (args 6)) len) = none := by
      intro nB length key
      obtain ⟨valid, modulus, power⟩ := pre_of_some length h.lower key
      change wv u.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len) = Spec.Rsa.os2ip nB at modulus
      change wv u.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len) =
        2 ^ (128 * Spec.Rsa.modulusWords len) % Spec.Rsa.os2ip nB at power
      have facts := valid_facts valid h.lower
      have good : precomputedAccepted (wv u.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len))
          (wv u.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len)) = true := by
        rw [modulus, power]
        exact decide_eq_true ⟨facts.2.1, Nat.mod_lt _ (by omega), facts.1⟩
      simp only [good, Bool.not_true, Bool.false_eq_true] at rejected
    refine WP.mono (precomputedFailure_post hu failed) fun t ⟨Post, Keep⟩ => ?_
    exact ⟨precomputedPost_compose h Os Post, (K.mono (by decide)).trans Keep⟩
  · intro accepted
    refine WP.mono (precomputedApply_post hu Nu Ru (by rw [precomputedCheck_exponent O, EB, E])
      (by rw [EB]; exact validE) (by simpa only [Bool.not_eq_false'] using accepted)) fun t ⟨Post, Keep⟩ => ?_
    exact ⟨precomputedPost_compose h Os Post, (K.mono (by decide)).trans Keep⟩

end VG.Proof.Bignum.X86.PublicContext
