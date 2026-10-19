module
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSized
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedDispatch
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedWidth
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPostFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # A valid public exponent reaches the selected packed-key width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedValid_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (exponent : e = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid e = true)
    (he : e < 2 ^ 33) (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (exponentHigh e)) :
    WP isa VG.Impl.Bignum.X86.PrecomputedFn.valid s fun t => PrecomputedPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have space := h.space
  have nw := h.scratch.nowrap
  unfold VG.Impl.Bignum.X86.PrecomputedFn.valid
  refine WP.seq (WP.mono (saveExponent_ok h.scratch (by omega) he lo hi) fun v ⟨E, O, K⟩ => ?_)
  have hv := h.keep K (by decide) (by decide) (O.mono (by omega) (by omega))
  refine WP.seq (WP.mono (precomputedWidth_ok h.upper (by rw [← h.outLen]; exact (hv.stack 1 (by decide)).readSrc))
    fun w ⟨Width, M, T⟩ => ?_)
  refine precomputedDispatch_ok VG.Impl.Bignum.X86.PublicFn.widths (publicWidths_member h.lower h.upper) ?_ Width ?_
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    have := List.mem_range.mp hi
    omega
  · intro u Ku Mu
    have Ksu : Keeps [.eax] s u := ((K.mono (by decide)).trans T).trans (Ku.mono (by decide))
    have Osu : Outside base 128 8 s.mem u.mem := by rw [Mu, M]; exact O
    have Osu' : Outside base 0 bytes s.mem u.mem := Osu.mono (by omega) (by omega)
    have hu := h.keep Ksu (by decide) (by decide) Osu'
    have EB := scratch_bytes Osu' (by have := h.eBound; have := h.upper; omega) h.eApart
    have Eu : val32 u.mem base 128 2 = e := by rw [Mu, M, E]
    refine WP.mono (precomputedSized_ok hu (by rw [Eu, EB, ← exponent])
      (by rw [EB, ← exponent]; exact validE)) fun t ⟨Post, Keep⟩ => ?_
    exact ⟨precomputedPost_compose h (Osu.mono (by omega) (by omega)) Post, (Ksu.mono (by decide)).trans Keep⟩

end VG.Proof.Bignum.X86.PublicContext
