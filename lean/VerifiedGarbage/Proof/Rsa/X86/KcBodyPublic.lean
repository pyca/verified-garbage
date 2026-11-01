module

public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.KcResult

import VerifiedGarbage.Proof.Rsa.X86.KcPublic
import VerifiedGarbage.Proof.Rsa.X86.KcSized
import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.TCB.X86.Isa

/-! # Public rejection branches and full key validation have the same result contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

def Post (g : CallGeometry) (m : Mem) (t : State) : Prop := Inputs g t ∧
  t.gpr .eax = BitVec.ofNat 32 (validity g.full (g.args 1).toNat (numbers g m)).toNat ∧
  Outside g.base 16 (g.size - 16) m t.mem

theorem checkExponent_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem))
    (hm : Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat = true) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.checkExponent g.full) s fun t => Post g s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.checkExponent
  refine WP.seq (WP.mono (exponent_ok h) fun u ⟨value, memU, restU⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ value) fun v ⟨flag, memV, restV⟩ => ?_)
  have mem : v.mem = s.mem := memV.trans memU
  have rest := restU.trans (restV.mono (by decide))
  have hv := h.after rest (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (!Spec.Rsa.exponentValid (numbers g s.mem).e) flag ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid (numbers g s.mem).e = false := by simpa using bad
    refine WP.mono (failure_ok hv) fun t ⟨ht, zero, mt, rt⟩ => ?_
    refine ⟨⟨ht, ?_, ?_⟩, rest.trans (rt.mono (by decide))⟩
    · rw [invalid_exponent _ _ _ invalid]; exact zero
    · rw [mt, mem]; exact Outside.refl _ _ _ _
  · intro good
    have accepted : Spec.Rsa.exponentValid (numbers g s.mem).e = true := by simpa using good
    refine WP.mono (sized_ok hv len (mem ▸ b) (mem ▸ hm) (mem ▸ accepted))
      fun t ⟨ht, value, frame, rt⟩ => ?_
    exact ⟨⟨ht, mem ▸ value, mem ▸ frame⟩, rest.trans rt⟩

theorem body_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem)) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.body g.full) s fun t => Post g s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.body
  refine WP.seq (WP.mono (modulus_ok h len.lower len.upper) fun u ⟨flag, mem, rest⟩ => ?_)
  have hu := h.after rest (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat) flag ?_ ?_
  · intro accepted
    refine WP.mono (checkExponent_ok hu len (mem ▸ b) (mem ▸ accepted)) fun t ⟨post, rt⟩ => ?_
    exact ⟨mem ▸ post, rest.trans rt⟩
  · intro rejected
    refine WP.mono (failure_ok hu) fun t ⟨ht, zero, mt, rt⟩ => ?_
    refine ⟨⟨ht, ?_, ?_⟩, rest.trans (rt.mono (by decide))⟩
    · rw [invalid_modulus _ _ _ rejected]; exact zero
    · rw [mt, mem]; exact Outside.refl _ _ _ _
end VG.Proof.Rsa.X86.KeyCheck
